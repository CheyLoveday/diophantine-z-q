import ZInQKernel.Contrib.CloudB3RC53.BaseZeroEndToEnd.TwoTerm

/-!
# Base zero end to end: from the retained data on the primitive complex to `ũ₀(0) = 0`

Lemma `ex:arith-base-zero` (`diophantine_zq.tex`, tex L4330–4373; the unit-disk step L4346–4366).
`baseZeroEndToEnd` starts from the primitive complex at the base, in the central lane's form
`[A^{m+1} --D--> A^{m+1}]` (degrees one and two; `RC/Central/BaseZero.lean`), over a DVR `A` with a
residue map `ρ` and central dimensions `(1, 1)` (`rank (D ⊗ ρ) = m`), together with its **own**
retained cycle `z`, closed functional `w` and class-functional coordinate `u_prim`, exactly as in
the hypotheses of `baseZero_core`, and:

1. encodes the complex as a graded complex (`TwoTerm.lean`), computes its central dimensions and
   applies the minimal-model split (`MinimalComplexes/MinimalModel.lean`, through
   `centralTwoTermModelAt_proof`): a degree-preserving change of bases to unit disks plus the
   minimal part `[A --δ--> A]`, `δ ∈ 𝔪`;
2. reads off integral `P, Q` (invertible) with `P D Q = diag(δ, 1, …, 1)` (degree-two and degree-one
   blocks of the graded change of bases, followed by permutations matching the unit disks);
3. constructs the `1 × 1` data `z₁ = (Q⁻¹ z)₀`, `w₁ = (w P⁻¹)₀`, `u₁ = z₁ w₁` and proves that they
   satisfy every hypothesis of `baseZero_core` with `m = 0` (cycle, coordinate, `rank (δ ⊗ ρ) = 0`,
   vanishing central cycle);
4. applies `baseZero_core` to them;
5. transports "regular, zero at the centre" back to `u_prim` through
   `CoordinateCancelRegularZero` (`u_prim = ι(det P · det Q) u₁`), and to the corrected coordinate
   `ι(ε₀) u_prim`.

**Classification.** PROVED (GLUE of `MinimalComplexes/` and `RC/Central/BaseZero.lean`).
-/

set_option linter.deprecated false

namespace ZInQ.Contrib.CloudB3RC53.BaseZeroEndToEnd

open Matrix ZInQ.Contrib.CloudB3RC53.MinimalComplexes ZInQ.Manuscript.RC.Central

variable {R : Type} [CommRing R] {m : ℕ}

/-! ### Blocks of a degree-preserving change of bases -/

/-- The degree-two block. -/
def blk2 (P : Matrix (TT m) (TT m) R) : Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
  Matrix.of fun i j => P (Sum.inr i) (Sum.inr j)

/-- The degree-one block. -/
def blk1 (P : Matrix (TT m) (TT m) R) : Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
  Matrix.of fun i j => P (Sum.inl i) (Sum.inl j)

theorem degP_inr_inl {P : Matrix (TT m) (TT m) R} (hP : IsDegPreserving (ttDeg m) P)
    (i j : Fin (m + 1)) : P (Sum.inr i) (Sum.inl j) = 0 := by
  by_contra h
  have := hP _ _ h
  simp [ttDeg] at this

theorem degP_inl_inr {P : Matrix (TT m) (TT m) R} (hP : IsDegPreserving (ttDeg m) P)
    (i j : Fin (m + 1)) : P (Sum.inl i) (Sum.inr j) = 0 := by
  by_contra h
  have := hP _ _ h
  simp [ttDeg] at this

theorem conj_inr_inl {P Q : Matrix (TT m) (TT m) R} (hP : IsDegPreserving (ttDeg m) P)
    (hQ : IsDegPreserving (ttDeg m) Q) (D : Matrix (Fin (m + 1)) (Fin (m + 1)) R)
    (i j : Fin (m + 1)) :
    (P * ttDiff D * Q) (Sum.inr i) (Sum.inl j) = (blk2 P * D * blk1 Q) i j := by
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, degP_inr_inl hP, degP_inr_inl hQ, zero_mul,
    mul_zero, Finset.sum_const_zero, zero_add, add_zero, blk2, blk1, of_apply, ttDiff,
    fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply]

theorem blk2_mul {P Q : Matrix (TT m) (TT m) R} (hP : IsDegPreserving (ttDeg m) P)
    (h : P * Q = 1) : blk2 P * blk2 Q = 1 := by
  ext i j
  have := congrFun (congrFun h (Sum.inr i)) (Sum.inr j)
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, degP_inr_inl hP, zero_mul,
    Finset.sum_const_zero, zero_add, Matrix.one_apply, Sum.inr.injEq] at this
  simpa [Matrix.mul_apply, blk2, Matrix.one_apply] using this

theorem blk1_mul {P Q : Matrix (TT m) (TT m) R} (hP : IsDegPreserving (ttDeg m) P)
    (h : P * Q = 1) : blk1 P * blk1 Q = 1 := by
  ext i j
  have := congrFun (congrFun h (Sum.inl i)) (Sum.inl j)
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, degP_inl_inr hP, zero_mul,
    Finset.sum_const_zero, add_zero, Matrix.one_apply, Sum.inl.injEq] at this
  simpa [Matrix.mul_apply, blk1, Matrix.one_apply] using this

theorem isUnit_det_of_mul_eq_one {M N : Matrix (Fin (m + 1)) (Fin (m + 1)) R} (h : M * N = 1) :
    IsUnit M.det :=
  isUnit_det_of_right_inverse h

/-! ### Reindexing by permutations -/

theorem submatrix_eq_mul (E : Matrix (Fin (m + 1)) (Fin (m + 1)) R) (σ₂ σ₁ : Equiv.Perm (Fin (m + 1))) :
    E.submatrix σ₂ σ₁ =
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) R).submatrix σ₂ id * E *
        (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) R).submatrix id σ₁ := by
  ext i j
  simp [Matrix.mul_apply, Matrix.one_apply, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem isUnit_det_perm_left (σ : Equiv.Perm (Fin (m + 1))) :
    IsUnit ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) R).submatrix σ id).det := by
  rw [det_permute, det_one, mul_one]
  exact (Units.map (Int.castRingHom R).toMonoidHom (Equiv.Perm.sign σ)).isUnit

theorem isUnit_det_perm_right (σ : Equiv.Perm (Fin (m + 1))) :
    IsUnit ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) R).submatrix id σ).det := by
  rw [det_permute', det_one, mul_one]
  exact (Units.map (Int.castRingHom R).toMonoidHom (Equiv.Perm.sign σ)).isUnit

/-! ### The Smith form `diag(δ, 1, …, 1)` from the split form -/

variable [IsLocalRing R]

/-- **From the minimal-model split to `P D Q = diag(δ, 1, …, 1)`.** For a two-term complex with
`rank (D ⊗ ρ) = m`, there are integral `P, Q` with unit determinants and `δ ∈ 𝔪` such that
`P D Q = diag(δ, 1, …, 1)`; they come from the degree-preserving change of bases of the
minimal-model split of the graded complex (`centralTwoTermModelAt_proof`). -/
theorem smith_of_split {k : Type} [Field k] (ρ : R →+* k)
    (hρ : ∀ x ∈ IsLocalRing.maximalIdeal R, ρ x = 0) (D : Matrix (Fin (m + 1)) (Fin (m + 1)) R)
    (hcentral : (D.map ρ).rank = m) :
    ∃ (P Q : Matrix (Fin (m + 1)) (Fin (m + 1)) R) (δ : R), IsUnit P.det ∧ IsUnit Q.det ∧
      P * D * Q = Matrix.diagonal (Fin.cons δ (fun _ => 1) : Fin (m + 1) → R) ∧
      δ ∈ IsLocalRing.maximalIdeal R := by
  classical
  obtain ⟨h0, h1, h2⟩ := resDimAt_tt ρ D hcentral
  obtain ⟨P, Q, kind, partner, s₁, s₂, hPQ, hQP, hP, hQ, hS, hk₁, hk₂, hd₁, hd₂, hmin, hδ, -⟩ :=
    centralTwoTermModelAt_proof R k ρ hρ (TT m) (ttDeg m) (ttDiff D) (ttDiff_graded D)
      (ttDiff_sq D) h0 h1 h2
  set E := blk2 P * D * blk1 Q with hE
  have hEe : ∀ i j, E i j = (P * ttDiff D * Q) (Sum.inr i) (Sum.inl j) := fun i j =>
    (conj_inr_inl hP hQ D i j).symm
  -- the minimal indices
  obtain ⟨j₁, rfl⟩ : ∃ j₁, s₁ = Sum.inl j₁ := by
    rcases s₁ with j | j
    · exact ⟨j, rfl⟩
    · exact absurd hd₁ (by simp [ttDeg])
  obtain ⟨j₂, rfl⟩ : ∃ j₂, s₂ = Sum.inr j₂ := by
    rcases s₂ with j | j
    · exact absurd hd₂ (by simp [ttDeg])
    · exact ⟨j, rfl⟩
  have hgD : IsGradedDiff (ttDeg m) (P * ttDiff D * Q) := IsGradedDiff.conj hP (ttDiff_graded D) hQ
  obtain ⟨s1, s2, s3, -⟩ := hS
  -- degree-one indices other than `s₁` are disk sources with partner in degree two
  have hsrc : ∀ j, j ≠ j₁ → kind (Sum.inl j) = 1 := by
    intro j hj
    have hk0 : kind (Sum.inl j) ≠ 0 := by
      intro h
      rcases hmin _ h with h' | h'
      · exact hj (Sum.inl.inj h')
      · exact Sum.inl_ne_inr h'
    have hk2 : kind (Sum.inl j) ≠ 2 := by
      intro h
      obtain ⟨hk, hpp⟩ := s2 _ h
      have hne := (s1 _ hk).2.2
      rw [hpp] at hne
      have := hgD _ _ (by rw [hne]; exact one_ne_zero)
      rcases hpart : partner (Sum.inl j) with a | a <;> rw [hpart] at this <;> simp [ttDeg] at this
    omega
  have hpart : ∀ j, j ≠ j₁ → ∃ j', partner (Sum.inl j) = Sum.inr j' := by
    intro j hj
    have hne := (s1 _ (hsrc j hj)).2.2
    have := hgD _ _ (by rw [hne]; exact one_ne_zero)
    rcases hp : partner (Sum.inl j) with a | a
    · rw [hp] at this; simp [ttDeg] at this
    · exact ⟨a, rfl⟩
  -- the matching `τ` of degree-one to degree-two indices
  let idx : TT m → Fin (m + 1) := Sum.elim (fun _ => 0) id
  let τ : Fin (m + 1) → Fin (m + 1) := fun j => if j = j₁ then j₂ else idx (partner (Sum.inl j))
  have hτpart : ∀ j, j ≠ j₁ → Sum.inr (τ j) = partner (Sum.inl j) := by
    intro j hj
    obtain ⟨j', hj'⟩ := hpart j hj
    simp only [τ, if_neg hj, hj', idx, Sum.elim_inr, id]
  have hτinj : Function.Injective τ := by
    intro a b hab
    by_cases ha : a = j₁ <;> by_cases hb : b = j₁
    · rw [ha, hb]
    · exfalso
      have e := hτpart b hb
      rw [← hab, ha] at e
      simp only [τ, if_pos rfl] at e
      have := (s1 _ (hsrc b hb)).1
      rw [← e] at this
      rw [hk₂] at this
      exact absurd this (by decide)
    · exfalso
      have e := hτpart a ha
      rw [hab, hb] at e
      simp only [τ, if_pos rfl] at e
      have := (s1 _ (hsrc a ha)).1
      rw [← e] at this
      rw [hk₂] at this
      exact absurd this (by decide)
    · have ea := hτpart a ha
      have eb := hτpart b hb
      rw [hab, eb] at ea
      have := congrArg partner ea
      rw [(s1 _ (hsrc a ha)).2.1, (s1 _ (hsrc b hb)).2.1] at this
      exact (Sum.inl.inj this).symm
  let στ : Equiv.Perm (Fin (m + 1)) := Equiv.ofBijective τ (Finite.injective_iff_bijective.mp hτinj)
  let σ₁ : Equiv.Perm (Fin (m + 1)) := Equiv.swap 0 j₁
  let σ₂ : Equiv.Perm (Fin (m + 1)) := σ₁.trans στ
  have hσ₁0 : σ₁ 0 = j₁ := Equiv.swap_apply_left 0 j₁
  have hσ₂ : ∀ i, σ₂ i = τ (σ₁ i) := fun i => rfl
  -- the reindexed block is `diag(δ, 1, …, 1)`
  set δ := E j₂ j₁ with hδdef
  have hdiag : E.submatrix σ₂ σ₁ = Matrix.diagonal (Fin.cons δ (fun _ => 1) : Fin (m + 1) → R) := by
    ext i j
    rw [submatrix_apply, hσ₂]
    by_cases hij : i = j
    · subst hij
      rw [diagonal_apply_eq]
      by_cases hi : i = 0
      · subst hi
        rw [hσ₁0]
        simp only [τ, if_pos rfl, Fin.cons_zero]
        rfl
      · obtain ⟨l, rfl⟩ := Fin.exists_succ_eq.mpr hi
        rw [Fin.cons_succ]
        have hne : σ₁ l.succ ≠ j₁ := by
          rw [← hσ₁0]; exact fun h => hi (σ₁.injective h)
        rw [hEe, hτpart _ hne]
        exact (s1 _ (hsrc _ hne)).2.2
    · rw [diagonal_apply_ne _ hij]
      by_contra hne
      rw [hEe] at hne
      rcases s3 _ _ hne with ⟨ka, kb⟩ | ⟨ka, hb⟩
      · -- both minimal: `σ₁ j = j₁` and `τ (σ₁ i) = j₂`
        rcases hmin _ ka with h | h
        · have hj : σ₁ j = j₁ := Sum.inl.inj h
          rcases hmin _ kb with h' | h'
          · exact Sum.inr_ne_inl h'
          · have hτi : τ (σ₁ i) = j₂ := Sum.inr.inj h'
            have : τ (σ₁ i) = τ (σ₁ j) := by rw [hτi, hj]; simp [τ]
            exact hij (σ₁.injective (hτinj this))
        · exact Sum.inl_ne_inr h
      · -- a disk entry: `τ (σ₁ i) = τ (σ₁ j)`
        have hjne : σ₁ j ≠ j₁ := by
          intro h
          rw [h] at ka
          rw [hk₁] at ka
          exact absurd ka (by decide)
        have : (Sum.inr (τ (σ₁ i)) : TT m) = Sum.inr (τ (σ₁ j)) := by rw [hb, hτpart _ hjne]
        exact hij (σ₁.injective (hτinj (Sum.inr.inj this)))
  refine ⟨(1 : Matrix (Fin (m + 1)) (Fin (m + 1)) R).submatrix σ₂ id * blk2 P,
    blk1 Q * (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) R).submatrix id σ₁, δ, ?_, ?_, ?_, ?_⟩
  · rw [det_mul]
    exact (isUnit_det_perm_left σ₂).mul (isUnit_det_of_mul_eq_one (blk2_mul hP hPQ))
  · rw [det_mul]
    exact (isUnit_det_of_mul_eq_one (blk1_mul hQ hQP)).mul (isUnit_det_perm_right σ₁)
  · rw [← hdiag, submatrix_eq_mul, hE]
    simp only [Matrix.mul_assoc]
  · rw [hδdef, hEe]
    exact hδ

/-! ### The end-to-end base-zero theorem -/

variable {A F : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field F] [Algebra A F] [IsFractionRing A F] {k : Type} [Field k]

/-- **Lemma `ex:arith-base-zero` end to end** (tex L4330–4373). Let `A` be a DVR with fraction field
`F` (`ι = algebraMap A F`) and residue map `ρ` killing `𝔪`; let `[A^{m+1} --D--> A^{m+1}]` be the
primitive complex at the base (degrees one and two) with central dimensions `(1, 1)`
(`rank (D ⊗ ρ) = m`), retained integral cycle `z` (`D z = 0`), integral closed functional `w`
(`w D = 0`) and generic class-functional coordinate `u_prim` (`z ⊗ w = u_prim · adj D` over `F`),
and assume the central cycle vanishes (`ρ z = 0`). Then:
* the minimal-model split gives integral `P, Q` with unit determinants and `δ ∈ 𝔪` with
  `P D Q = diag(δ, 1, …, 1)`;
* the cancelled `1 × 1` data `D₁ = (δ)`, `z₁ = (Q⁻¹ z)₀`, `w₁ = (w P⁻¹)₀`, `u₁ = ι(z₁ w₁)` satisfy all
  hypotheses of `baseZero_core` with `m = 0`;
* `u_prim = ι(det P · det Q) u₁`;
* `u_prim` is regular with value `0` at the centre, and so is `ι(ε₀) u_prim`, obtained by applying
  `baseZero_core` to the `1 × 1` data and transporting back through `CoordinateCancelRegularZero`. -/
theorem baseZeroEndToEnd (ρ : A →+* k) (hρ : ∀ x ∈ IsLocalRing.maximalIdeal A, ρ x = 0)
    (D : Matrix (Fin (m + 1)) (Fin (m + 1)) A) (hcentral : (D.map ρ).rank = m)
    (z w : Fin (m + 1) → A) (hz : D *ᵥ z = 0) (hw : w ᵥ* D = 0) (uprim : F)
    (hu : IsClassFunctionalCoord (D.map (algebraMap A F)) (fun i => algebraMap A F (z i))
      (fun i => algebraMap A F (w i)) uprim)
    (hz0 : ∀ i, ρ (z i) = 0) (ε₀ : A) :
    ∃ (P Q : Matrix (Fin (m + 1)) (Fin (m + 1)) A) (δ : A),
      IsUnit P.det ∧ IsUnit Q.det ∧
      P * D * Q = Matrix.diagonal (Fin.cons δ (fun _ => 1) : Fin (m + 1) → A) ∧
      δ ∈ IsLocalRing.maximalIdeal A ∧
      let D₁ : Matrix (Fin (0 + 1)) (Fin (0 + 1)) A := Matrix.of fun _ _ => δ
      let z₁ : Fin (0 + 1) → A := fun _ => (Q⁻¹ *ᵥ z) 0
      let w₁ : Fin (0 + 1) → A := fun _ => (w ᵥ* P⁻¹) 0
      let u₁ : F := algebraMap A F ((Q⁻¹ *ᵥ z) 0 * (w ᵥ* P⁻¹) 0)
      ((D₁.map ρ).rank = 0 ∧ D₁ *ᵥ z₁ = 0 ∧
        IsClassFunctionalCoord (D₁.map (algebraMap A F)) (fun i => algebraMap A F (z₁ i))
          (fun i => algebraMap A F (w₁ i)) u₁ ∧ (∀ i, ρ (z₁ i) = 0)) ∧
      uprim = algebraMap A F (P.det * Q.det) * u₁ ∧
      (∃ u₀ : A, algebraMap A F u₀ = uprim ∧ ρ u₀ = 0) ∧
      (∃ a : A, algebraMap A F a = algebraMap A F ε₀ * uprim ∧ ρ a = 0) := by
  obtain ⟨P, Q, δ, hP, hQ, hD, hδ⟩ := smith_of_split ρ hρ D hcentral
  refine ⟨P, Q, δ, hP, hQ, hD, hδ, ?_⟩
  intro D₁ z₁ w₁ u₁
  set ι := algebraMap A F
  -- the `1 × 1` hypotheses
  have hrank : (D₁.map ρ).rank = 0 := by
    have : D₁.map ρ = 0 := by
      ext i j
      simp only [D₁, map_apply, of_apply, Matrix.zero_apply]
      exact hρ _ hδ
    rw [this, rank_zero]
  have hz₁ : D₁ *ᵥ z₁ = 0 := by
    have h := congrFun (show (P * D * Q) *ᵥ (Q⁻¹ *ᵥ z) = 0 by
      rw [mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_nonsing_inv Q hQ, Matrix.mul_one,
        ← mulVec_mulVec, hz, mulVec_zero]) 0
    rw [hD, mulVec_diagonal, Fin.cons_zero] at h
    have h' : δ * (Q⁻¹ *ᵥ z) 0 = 0 := h
    ext i
    rw [mulVec, dotProduct, Fin.sum_univ_one]
    exact h'
  have hu₁ : IsClassFunctionalCoord (D₁.map ι) (fun i => ι (z₁ i)) (fun i => ι (w₁ i)) u₁ := by
    unfold IsClassFunctionalCoord
    ext i j
    fin_cases i; fin_cases j
    simp [vecMulVec_apply, adjugate_fin_one, u₁, z₁, w₁, ι, map_mul]
  have hz₁0 : ∀ i, ρ (z₁ i) = 0 := by
    intro i
    simp only [z₁, mulVec, dotProduct, map_sum, map_mul, hz0, mul_zero, Finset.sum_const_zero]
  refine ⟨⟨hrank, hz₁, hu₁, hz₁0⟩, ?_⟩
  -- `baseZero_core` on the `1 × 1` data
  obtain ⟨⟨u₀, hu₀, hρu₀⟩, -⟩ := baseZero_core (F := F) ρ hρ D₁ hrank z₁ w₁ hz₁ u₁ hu₁ hz₁0 ε₀
  -- transport back through the unit `det P · det Q`
  have hu₁' : IsClassFunctionalCoord (Matrix.of fun _ _ => ι δ : Matrix (Fin 1) (Fin 1) F)
      (fun _ => ι ((Q⁻¹ *ᵥ z) 0)) (fun _ => ι ((w ᵥ* P⁻¹) 0)) u₁ := hu₁
  obtain ⟨huprim, htrans⟩ := coordinateCancelRegularZero_proof A F k ι ρ m D P Q δ z w uprim u₁
    hP hQ hD hz hw hu hu₁'
  obtain ⟨v₀, hv₀, hρv₀⟩ := htrans ⟨u₀, hu₀, hρu₀⟩
  exact ⟨huprim, ⟨v₀, hv₀, hρv₀⟩,
    ⟨ε₀ * v₀, by rw [map_mul, hv₀], by rw [map_mul, hρv₀, mul_zero]⟩⟩

end ZInQ.Contrib.CloudB3RC53.BaseZeroEndToEnd

import ZInQKernel.Contrib.CloudB3RC53.Torsion.Cone

/-!
# Torsion, part 9: invariance of the Knudsen–Mumford coordinate under quasi-isomorphisms

* `FourMap C D`: a chain map of four-term complexes (matrices `f⁰, …, f³` commuting with the
  differentials).
* `FourMap.augMap`: **the augmented compatibility** — if `f¹ z_C = z_D` and `λ_D f² = λ_C`, then `f`
  extended by the identity on the two augmentation lines is a chain map of the augmented based
  complexes (`ChainMapB`).
* **`kmCoord_eq_of_cone` (PROVED)**: for a chain map of the augmented complexes of two four-term
  complexes whose augmented complexes are acyclic,
  `kmCoord(C, z_C, λ_C) = (−1)^{|κo|} · kmCoord(D, z_D, λ_D) · τ(cone f)⁻¹`; in particular the
  coordinate changes by the inverse torsion of the cone (up to sign), a unit.
* `kmCoord_eq_of_fourMap`: the same for a `FourMap` with the augmented compatibility.
* `cone_id_example` (non-vacuity): the identity of the augmented two-term example
  (`twoTermContraction_example`) is such a chain map.

**Classification.** PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.Torsion

open Matrix

variable {K : Type*} [Field K]

/-! ### The coordinate through a cone -/

section Coord

variable {ι0 ι1 ι2 ι3 ι0' ι1' ι2' ι3' : Type*}
  [Fintype ι0] [Fintype ι1] [Fintype ι2] [Fintype ι3]
  [Fintype ι0'] [Fintype ι1'] [Fintype ι2'] [Fintype ι3']
  [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3]
  [DecidableEq ι0'] [DecidableEq ι1'] [DecidableEq ι2'] [DecidableEq ι3']

/-- **The coordinate changes by the inverse torsion of the cone** (PROVED): for a chain map `f` of
the augmented complexes, both acyclic,
`kmCoord(C) = (−1)^{|κo(aug C)|} · kmCoord(D) · τ(cone f)⁻¹`. -/
theorem kmCoord_eq_of_cone (C : FourCx K ι0 ι1 ι2 ι3) (D : FourCx K ι0' ι1' ι2' ι3')
    (zC : ι1 → K) (lC : ι2 → K) (hzC : C.d1 *ᵥ zC = 0) (hlC : lC ᵥ* C.d1 = 0)
    (zD : ι1' → K) (lD : ι2' → K) (hzD : D.d1 *ᵥ zD = 0) (hlD : lD ᵥ* D.d1 = 0)
    (f : ChainMapB (C.aug zC lC hzC hlC).toBased (D.aug zD lD hzD hlD).toBased)
    (hC : Contraction (C.aug zC lC hzC hlC).toBased)
    (hD : Contraction (D.aug zD lD hzD hlD).toBased)
    (σC : (ι0 ⊕ Unit) ⊕ ι2 ≃ ι1 ⊕ (ι3 ⊕ Unit)) (σD : (ι0' ⊕ Unit) ⊕ ι2' ≃ ι1' ⊕ (ι3' ⊕ Unit)) :
    kmCoord C zC lC hzC hlC σC =
      (-1) ^ Fintype.card (ι1 ⊕ (ι3 ⊕ Unit)) * kmCoord D zD lD hzD hlD σD *
        (torsion (BasedCx.cone f) (σD.sumCongr σC.symm))⁻¹ := by
  unfold kmCoord
  rw [torsion_eq_of_cone f hC hD σD σC]
  ring

end Coord

/-! ### Chain maps of four-term complexes and the augmented compatibility -/

section FourMap

variable {ι0 ι1 ι2 ι3 ι0' ι1' ι2' ι3' : Type*}
  [Fintype ι0] [Fintype ι1] [Fintype ι2] [Fintype ι3]
  [Fintype ι0'] [Fintype ι1'] [Fintype ι2'] [Fintype ι3']
  [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3]
  [DecidableEq ι0'] [DecidableEq ι1'] [DecidableEq ι2'] [DecidableEq ι3']

/-- **A chain map of four-term complexes.** -/
structure FourMap (C : FourCx K ι0 ι1 ι2 ι3) (D : FourCx K ι0' ι1' ι2' ι3') where
  f0 : Matrix ι0' ι0 K
  f1 : Matrix ι1' ι1 K
  f2 : Matrix ι2' ι2 K
  f3 : Matrix ι3' ι3 K
  c0 : D.d0 * f0 = f1 * C.d0
  c1 : D.d1 * f1 = f2 * C.d1
  c2 : D.d2 * f2 = f3 * C.d2

variable {C : FourCx K ι0 ι1 ι2 ι3} {D : FourCx K ι0' ι1' ι2' ι3'}

/-- **The augmented compatibility**: `f` extended by the identity on the augmentation lines is a
chain map of the augmented based complexes when `f¹ z_C = z_D` and `λ_D f² = λ_C`. -/
def FourMap.augMap (F : FourMap C D) (zC : ι1 → K) (lC : ι2 → K) (hzC : C.d1 *ᵥ zC = 0)
    (hlC : lC ᵥ* C.d1 = 0) (zD : ι1' → K) (lD : ι2' → K) (hzD : D.d1 *ᵥ zD = 0)
    (hlD : lD ᵥ* D.d1 = 0) (hz : F.f1 *ᵥ zC = zD) (hl : lD ᵥ* F.f2 = lC) :
    ChainMapB (C.aug zC lC hzC hlC).toBased (D.aug zD lD hzD hlD).toBased where
  fE := fromBlocks (fromBlocks F.f0 0 0 1) 0 0 F.f2
  fO := fromBlocks F.f1 0 0 (fromBlocks F.f3 0 0 1)
  deg_fE := by
    rintro ((i | i) | i) ((j | j) | j) h
    all_goals first | rfl | exact absurd rfl h
  deg_fO := by
    rintro (i | (i | i)) (j | (j | j)) h
    all_goals first | rfl | exact absurd rfl h
  commOE := by
    ext (i | (i | i)) ((j | j) | j)
    · simpa [FourCx.toBased_dOE, FourCx.aug, mul_apply, Fintype.sum_sum_type] using
        congrFun (congrFun F.c0 i) j
    · simpa [FourCx.toBased_dOE, FourCx.aug, mul_apply, Fintype.sum_sum_type, mulVec,
        dotProduct] using (congrFun hz i).symm
    · simp [FourCx.toBased_dOE, FourCx.aug, mul_apply, Fintype.sum_sum_type]
    · simp [FourCx.toBased_dOE, FourCx.aug, mul_apply, Fintype.sum_sum_type]
    · simp [FourCx.toBased_dOE, FourCx.aug, mul_apply, Fintype.sum_sum_type]
    · simpa [FourCx.toBased_dOE, FourCx.aug, mul_apply, Fintype.sum_sum_type] using
        congrFun (congrFun F.c2 i) j
    · simp [FourCx.toBased_dOE, FourCx.aug, mul_apply, Fintype.sum_sum_type]
    · simp [FourCx.toBased_dOE, FourCx.aug, mul_apply, Fintype.sum_sum_type]
    · simpa [FourCx.toBased_dOE, FourCx.aug, mul_apply, Fintype.sum_sum_type, vecMul,
        dotProduct] using congrFun hl j
  commEO := by
    ext ((i | i) | i) (j | (j | j))
    all_goals simp [FourCx.toBased_dEO, FourCx.aug, mul_apply, Fintype.sum_sum_type]
    exact congrFun (congrFun F.c1 i) j

/-- **The coordinate through a chain map of four-term complexes** (PROVED). -/
theorem kmCoord_eq_of_fourMap (F : FourMap C D) (zC : ι1 → K) (lC : ι2 → K)
    (hzC : C.d1 *ᵥ zC = 0) (hlC : lC ᵥ* C.d1 = 0) (zD : ι1' → K) (lD : ι2' → K)
    (hzD : D.d1 *ᵥ zD = 0) (hlD : lD ᵥ* D.d1 = 0) (hz : F.f1 *ᵥ zC = zD) (hl : lD ᵥ* F.f2 = lC)
    (hC : Contraction (C.aug zC lC hzC hlC).toBased)
    (hD : Contraction (D.aug zD lD hzD hlD).toBased)
    (σC : (ι0 ⊕ Unit) ⊕ ι2 ≃ ι1 ⊕ (ι3 ⊕ Unit)) (σD : (ι0' ⊕ Unit) ⊕ ι2' ≃ ι1' ⊕ (ι3' ⊕ Unit)) :
    kmCoord C zC lC hzC hlC σC =
      (-1) ^ Fintype.card (ι1 ⊕ (ι3 ⊕ Unit)) * kmCoord D zD lD hzD hlD σD *
        (torsion (BasedCx.cone (F.augMap zC lC hzC hlC zD lD hzD hlD hz hl))
          (σD.sumCongr σC.symm))⁻¹ :=
  kmCoord_eq_of_cone C D zC lC hzC hlC zD lD hzD hlD _ hC hD σC σD

/-- **Retained bases compatible along `f`**: if the cone torsion is the canonical sign
`(−1)^{|κo(aug C)|}`, the coordinates agree (PROVED). -/
theorem kmCoord_eq_of_fourMap_retained (F : FourMap C D) (zC : ι1 → K) (lC : ι2 → K)
    (hzC : C.d1 *ᵥ zC = 0) (hlC : lC ᵥ* C.d1 = 0) (zD : ι1' → K) (lD : ι2' → K)
    (hzD : D.d1 *ᵥ zD = 0) (hlD : lD ᵥ* D.d1 = 0) (hz : F.f1 *ᵥ zC = zD) (hl : lD ᵥ* F.f2 = lC)
    (hC : Contraction (C.aug zC lC hzC hlC).toBased)
    (hD : Contraction (D.aug zD lD hzD hlD).toBased)
    (σC : (ι0 ⊕ Unit) ⊕ ι2 ≃ ι1 ⊕ (ι3 ⊕ Unit)) (σD : (ι0' ⊕ Unit) ⊕ ι2' ≃ ι1' ⊕ (ι3' ⊕ Unit))
    (hcone : torsion (BasedCx.cone (F.augMap zC lC hzC hlC zD lD hzD hlD hz hl))
      (σD.sumCongr σC.symm) = (-1) ^ Fintype.card (ι1 ⊕ (ι3 ⊕ Unit))) :
    kmCoord C zC lC hzC hlC σC = kmCoord D zD lD hzD hlD σD := by
  rw [kmCoord_eq_of_fourMap F zC lC hzC hlC zD lD hzD hlD hz hl hC hD σC σD, hcone]
  have hs : ((-1 : K) ^ Fintype.card (ι1 ⊕ (ι3 ⊕ Unit))) *
      (-1) ^ Fintype.card (ι1 ⊕ (ι3 ⊕ Unit)) = 1 := by
    rw [← pow_add]; exact Even.neg_one_pow ⟨_, rfl⟩
  have hne : (-1 : K) ^ Fintype.card (ι1 ⊕ (ι3 ⊕ Unit)) ≠ 0 :=
    pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  calc (-1) ^ Fintype.card (ι1 ⊕ (ι3 ⊕ Unit)) * kmCoord D zD lD hzD hlD σD *
        ((-1 : K) ^ Fintype.card (ι1 ⊕ (ι3 ⊕ Unit)))⁻¹
      = kmCoord D zD lD hzD hlD σD * ((-1 : K) ^ Fintype.card (ι1 ⊕ (ι3 ⊕ Unit)) *
          ((-1 : K) ^ Fintype.card (ι1 ⊕ (ι3 ⊕ Unit)))⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hne, mul_one]

/-- The identity chain map. -/
def FourMap.id (C : FourCx K ι0 ι1 ι2 ι3) : FourMap C C where
  f0 := 1
  f1 := 1
  f2 := 1
  f3 := 1
  c0 := by rw [Matrix.mul_one, Matrix.one_mul]
  c1 := by rw [Matrix.mul_one, Matrix.one_mul]
  c2 := by rw [Matrix.mul_one, Matrix.one_mul]

end FourMap

/-- **non-vacuity**: the hypotheses of `kmCoord_eq_of_fourMap` hold for the identity of the augmented
two-term example `D = (0)`, `z = λ = 1` (`twoTermContraction_example`). -/
theorem cone_id_example :
    kmCoord (twoTerm (0 : Matrix (Fin 1) (Fin 1) K)) 1 1 twoTerm_zero_hz twoTerm_zero_hw (σ₀ 1) =
      (-1) ^ Fintype.card (Fin 1 ⊕ (Empty ⊕ Unit)) *
        kmCoord (twoTerm (0 : Matrix (Fin 1) (Fin 1) K)) 1 1 twoTerm_zero_hz twoTerm_zero_hw
          (σ₀ 1) *
        (torsion (BasedCx.cone ((FourMap.id (twoTerm (0 : Matrix (Fin 1) (Fin 1) K))).augMap
          1 1 twoTerm_zero_hz twoTerm_zero_hw 1 1 twoTerm_zero_hz twoTerm_zero_hw
          (Matrix.one_mulVec _) (Matrix.vecMul_one _))) ((σ₀ 1).sumCongr (σ₀ 1).symm))⁻¹ :=
  kmCoord_eq_of_fourMap _ _ _ _ _ _ _ _ _ _ _ twoTermContraction_example
    twoTermContraction_example _ _

end ZInQ.Contrib.CloudB3RC53.Torsion

import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate4

/-!
**Theorem 5.3, Lane RC0 round 4: non-vacuity of the tightened (4.7) leaf at an unused prime**

The tightened leaf `CommonCoordinateTrianglesG` asks, at each unused prime `p` of the address, for a
Frobenius matrix of determinant `p` and a relaxation step that is a `NaturalStep` at `q = p`. Batch
3's examples have `q = 1`, so they do not inhabit it. Here:

* `selmerFunctionals_any e`: batch 3's retention example (`selmerFunctionals_example`) at an
  arbitrary point factor `e`: the triangular-basis functionals `(e, 0, 0, 0, 0)` and `(1)` are the
  paired functionals of retained Selmer data;
* `naturalStep_three`: a `NaturalStep` at `q = 3` over `ℚ₂[[t]]`: Frobenius `Fr = [[11/3, −3], [1, 0]]`
  (trace `11/3`, determinant `3`), `z = z⁻¹ = 1`, so `e_3 = 5/3` and the two-place block has
  determinant `1`; primitive model `(0)` with coordinate `1`, relaxed model `diag(0, 1, 1, 1, 1)`
  carried to the triangular model by `Q_R = diag(1, twoPlaceBlock)`, coordinate `e_3²`, and the step
  unit `ε = 3⁻⁴`; (4.7) reads `l_3 e_3² = e_3² · 3⁻⁴ · 1` with `l_3 = 3⁻⁴`;
* `trianglesG_three`, `nonempty_trianglesG_three`: `CommonCoordinateTrianglesG` at the address `0`
  of the family with the single graph prime `3` (so `3` is unused), for data with `u_prim = 1` and
  `ũ = η e_3²`.

Everything here is PROVED; nothing is used by the deduction.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open Matrix CategoryTheory ZInQ.Manuscript ZInQ.Manuscript.RC.Central ZInQ.Contrib.CloudB3RC53
  ZInQ.Contrib.CloudB3RC53.CommonCoordinate ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality

/-- **Batch 3's retention example at an arbitrary point factor** (PROVED): over `ℚ₂[[t]]`, the
place-by-place retention `examplePlaceRetention`, the trace `fst`, the strict class `(e, 0, 0)`, the
orthogonal class `(1, 0, 0)` and the cocycle `(1, 1, 0)` give the functionals `(e, 0, 0, 0, 0)` and
`(1)`. -/
theorem selmerFunctionals_any (e : KPS) :
    SelmerFunctionals (κ := Fin 2 ⊕ Fin 2) (Sum.elim (fun _ => e) (fun _ => 0))
      (fun _ : Fin 1 => (1 : KPS)) e := by
  refine ⟨CommRingCat.of KPS, relSel KPS, constSel KPS, constCx KPS, constCx KPS, constId KPS,
    constId KPS, examplePlaceRetention KPS,
    LinearMap.fst KPS ((constCx KPS).X 3) ((constCx KPS).X (3 - 1)), fun _ => rfl,
    (show selT _ 1 from (e, (0 : KPS), (0 : KPS))),
    (show selT _ 1 from ((1 : KPS), (0 : KPS), (0 : KPS))), e,
    (show selT _ 0 from ((0 : KPS), (0 : KPS), (0 : KPS))), ?_,
    fun _ => (show selT _ 2 from ((1 : KPS), (1 : KPS), (0 : KPS))), ?_,
    Sum.elim (fun _ => (changeMap (relSel KPS) (constId KPS)).f 2 2 rfl
      (show selT _ 2 from ((1 : KPS), (1 : KPS), (0 : KPS)))) (fun _ => 0), fun _ => rfl,
    RingHom.id KPS, ?_, ?_, ?_⟩
  · refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · change e = e * 1 + 0
      ring
    · change (0 : KPS) = e * 0 + 0
      ring
    · change (0 : KPS) = e * 0 + (0 - 0 - 0)
      ring
  · intro i
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · rfl
    · rfl
    · change (1 : KPS) - 1 - 0 = 0
      ring
  · rfl
  · rintro (j | j)
    · change e = e * 1
      ring
    · change (0 : KPS) = e * 0
      ring
  · intro i
    change (1 : KPS) = 1 * 1
    ring

/-! The step at `q = 3` -/

/-- The Frobenius matrix of the example: trace `11/3`, determinant `3`. -/
def frobThree : Matrix (Fin 2) (Fin 2) KPS :=
  !![PowerSeries.C (11 / 3 : ℚ_[2]), PowerSeries.C (-3 : ℚ_[2]); 1, 0]

/-- Its trace `a = 11/3`. -/
def aThree : KPS := PowerSeries.C (11 / 3 : ℚ_[2])

/-- The point factor `e = a − z − z⁻¹ = 5/3` at `z = 1`. -/
def eThree : KPS := pointFactor aThree 1 1

/-- The relaxed class and functional `(e, 0, 0, 0, 0)`. -/
def zThree : Fin 1 ⊕ (Fin 2 ⊕ Fin 2) → KPS := Sum.elim (fun _ => eThree) (fun _ => 0)

/-- The two-place block at `q = 3`, `z = z⁻¹ = 1`. -/
def blockThree : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) KPS :=
  twoPlaceBlock frobThree (PowerSeries.C ((3 : ℕ) : ℚ_[2])) 1 1

/-- The basis comparison `Q_R = diag(1, twoPlaceBlock)`. -/
def qThree : Matrix (Fin 1 ⊕ (Fin 2 ⊕ Fin 2)) (Fin 1 ⊕ (Fin 2 ⊕ Fin 2)) KPS :=
  fromBlocks 1 0 0 blockThree

theorem frobThree_trace : frobThree.trace = aThree := by
  simp [frobThree, aThree, Matrix.trace_fin_two_of]

theorem frobThree_det : frobThree.det = PowerSeries.C ((3 : ℕ) : ℚ_[2]) := by
  rw [frobThree, Matrix.det_fin_two_of, mul_zero, mul_one, zero_sub, ← map_neg, neg_neg,
    Nat.cast_ofNat]

theorem blockThree_det : blockThree.det = 1 := by
  rw [blockThree, det_twoPlaceBlock, quotientDet, det_smul_sub_smul_one, frobThree_det,
    frobThree_trace, aThree]
  have h : (1 : KPS) ^ 2 * PowerSeries.C ((3 : ℕ) : ℚ_[2]) -
      1 * PowerSeries.C ((3 : ℕ) : ℚ_[2]) * PowerSeries.C (11 / 3 : ℚ_[2]) +
        PowerSeries.C ((3 : ℕ) : ℚ_[2]) ^ 2 = 1 := by
    rw [one_pow, one_mul, ← map_mul, ← map_pow, ← map_sub, ← map_add,
      show ((3 : ℕ) : ℚ_[2]) - (3 : ℕ) * (11 / 3) + ((3 : ℕ) : ℚ_[2]) ^ 2 = 1 by norm_num,
      map_one]
  rw [h, one_mul]

theorem qThree_det : qThree.det = 1 := by
  rw [qThree, det_fromBlocks_zero₂₁, det_one, one_mul, blockThree_det]

theorem qThree_mulVec : qThree *ᵥ zThree = zThree := by
  rw [qThree, fromBlocks_mulVec]
  funext i
  rcases i with i | i
  · simp [zThree]
  · simp [zThree, Matrix.mulVec, dotProduct]

theorem qThree_inv_mulVec : qThree⁻¹ *ᵥ zThree = zThree := by
  conv_lhs => rw [← qThree_mulVec]
  rw [mulVec_mulVec, nonsing_inv_mul _ (by rw [qThree_det]; exact isUnit_one), one_mulVec]

theorem relaxed_three :
    (1 : Matrix (Fin 1 ⊕ (Fin 2 ⊕ Fin 2)) (Fin 1 ⊕ (Fin 2 ⊕ Fin 2)) KPS) *
        Matrix.diagonal exDiag * qThree =
      fromBlocks ((1 : Matrix (Fin 1) (Fin 1) KPS) * 0 * 1) 0 0 blockThree := by
  rw [← relaxed_example, twoPlaceBlock_example, qThree, Matrix.one_mul, fromBlocks_multiply]
  simp

/-- **A `NaturalStep` at `q = 3`** (PROVED): the retained functionals from
`selmerFunctionals_any`, a `Λ`-unit basis comparison of determinant `1`, `u_prim = 1`,
`u_rel = e²`, `ε = 3⁻⁴`. -/
theorem naturalStep_three :
    NaturalStep frobThree (PowerSeries.C ((3 : ℕ) : ℚ_[2])) (PowerSeries.C (((3 : ℕ) : ℚ_[2])⁻¹))
      aThree 1 1 1 (eThree * eThree) (PowerSeries.C (((3 : ℕ) : ℚ_[2])⁻¹) ^ 4) LamUnit
      LamUnit := by
  refine ⟨1, 0, 1, 1, Matrix.diagonal exDiag, 1, qThree, 0, fun _ => 1, fun _ => 1, zThree,
    zThree, by simp, by simp, by simp, by rw [qThree_det]; exact isUnit_one, relaxed_three, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [qThree_inv_mulVec, inv_one, one_mulVec]
    simp [zThree, eThree]
  · rw [inv_one, inv_one, vecMul_one, vecMul_one]
    exact selmerFunctionals_any eThree
  · -- the relaxed coordinate: `adj diag(0,1,1,1,1) = diag(1,0,0,0,0)`
    unfold IsCoordOn
    rw [adjugate_diagonal]
    ext x y
    rcases x with x | x <;> rcases y with y | y
    · fin_cases x; fin_cases y
      simp only [vecMulVec_apply, zThree, Sum.elim_inl, Matrix.smul_apply, diagonal_apply_eq,
        smul_eq_mul]
      rw [Finset.prod_eq_one]
      · rw [mul_one]
      · intro j hj
        rcases j with j | j
        · fin_cases j; exact absurd rfl (Finset.ne_of_mem_erase hj)
        · rfl
    · simp [vecMulVec_apply, diagonal_apply_ne, zThree]
    · simp [vecMulVec_apply, diagonal_apply_ne, zThree]
    · simp only [vecMulVec_apply, zThree, Sum.elim_inr, mul_zero, Matrix.smul_apply, smul_eq_mul]
      by_cases hxy : x = y
      · subst hxy
        rw [diagonal_apply_eq, Finset.prod_eq_zero (i := Sum.inl 0)]
        · simp
        · simp
        · rfl
      · rw [diagonal_apply_ne _ (fun h => hxy (Sum.inr_injective h)), mul_zero]
  · unfold IsClassFunctionalCoord
    ext i j
    fin_cases i; fin_cases j
    simp [vecMulVec_apply, adjugate_fin_one]
  · rw [Matrix.one_mul, Matrix.mul_one, adjugate_fin_one]
    exact one_ne_zero
  · rw [qThree_det]
    simpa using lamUnit_one
  · simpa using lamUnit_one
  · rw [qThree_det]
    simp

/-! The structure at the family with the single graph prime `3` -/

/-- The family of the example: one address bit, the single graph prime `3`, `λ_3(x) = x₀`. -/
def famThree : Family := ⟨1, {3}, fun _ => LinearMap.proj 0⟩

theorem unusedAt_famThree : unusedAt famThree 0 = {3} := unusedAt_zero famThree

/-- `l_3 = det(1 − 3⁻¹ Fr)²` at `z = 1`. -/
def lThree : KPS := quotientFactor frobThree (PowerSeries.C (((3 : ℕ) : ℚ_[2])⁻¹)) 1 1

/-- `e_3⁻¹ = 3/5`. -/
def eiThree : KPS := PowerSeries.C (3 / 5 : ℚ_[2])

/-- `v_3 = (l_3 e_3⁻² − 1)/2`. -/
def vThree : KPS := PowerSeries.C (1 / 2 : ℚ_[2]) * (lThree * eiThree ^ 2 - 1)

theorem two_mul_C_half_three : (2 : KPS) * PowerSeries.C (1 / 2 : ℚ_[2]) = 1 := by
  rw [show (2 : KPS) = PowerSeries.C (2 : ℚ_[2]) from (map_ofNat PowerSeries.C 2).symm, ← map_mul]
  norm_num

theorem eThree_mul_eiThree : eThree * eiThree = 1 := by
  rw [eThree, pointFactor, aThree, eiThree, ← map_one (PowerSeries.C (R := ℚ_[2])), ← map_sub,
    ← map_sub, ← map_mul, show ((11 / 3 : ℚ_[2]) - 1 - 1) * (3 / 5) = 1 by norm_num]

/-- **`CommonCoordinateTrianglesG` with one unused prime** (PROVED), at the address `0` of
`famThree`, for any data with `u_prim = 1` and `ũ = η e_3²` there. -/
def trianglesG_three {ℓ : ℕ} (D : RCData ℓ) (hP : D.uPrim famThree 0 = 1)
    (hT : D.uTilde famThree 0 =
      Central.eta ({3} : Finset ℕ) (fun _ => vThree) (fun _ => (1 : KPS)) * (eThree * eThree)) :
    CommonCoordinateTrianglesG D famThree 0 where
  R := KPS
  chi := RingHom.id KPS
  v _ := vThree
  g _ := 1
  l _ := lThree
  e _ := eThree
  ei _ := eiThree
  hchi q _ := by
    rw [map_zero (famThree.lam q)]
    simp
  hratio _ _ := by
    change lThree * eiThree ^ 2 = 1 + 2 * (PowerSeries.C (1 / 2 : ℚ_[2]) *
      (lThree * eiThree ^ 2 - 1))
    rw [← mul_assoc, two_mul_C_half_three]
    ring
  hinv _ _ := eThree_mul_eiThree
  urel := eThree * eThree
  hutilde := hT
  F _ := frobThree
  a _ := aThree
  z _ := 1
  zi _ := 1
  ha _ _ := frobThree_trace
  hd p hp := by
    rw [unusedAt_famThree, Finset.mem_singleton] at hp
    subst hp
    exact frobThree_det
  hzi _ _ := mul_one 1
  hl p hp := by
    rw [unusedAt_famThree, Finset.mem_singleton] at hp
    subst hp
    rfl
  he _ _ := rfl
  u T := if 3 ∈ T then eThree * eThree else 1
  hrel := by rw [unusedAt_famThree]; simp
  hprim := by simp [hP]
  eps _ := PowerSeries.C (((3 : ℕ) : ℚ_[2])⁻¹) ^ 4
  hstep T hT p hp hpT := by
    rw [unusedAt_famThree, Finset.mem_singleton] at hp
    subst hp
    have hT0 : T = ∅ := by
      ext q
      constructor
      · intro hq
        have h3 := hT hq
        rw [unusedAt_famThree, Finset.mem_singleton] at h3
        subst h3
        exact absurd hq hpT
      · simp
    subst hT0
    simp only [Finset.notMem_empty, Finset.mem_insert_self, ↓reduceIte]
    exact naturalStep_three

/-- Data with `u_prim = 1` and `ũ = η e_3²` at every family (the remaining fields are irrelevant to
the leaf). -/
def exDataThree : RCData 1 where
  S := ∅
  prepared _ := True
  Lstar _ := 1
  jgen _ := 0
  jrc _ _ := 0
  hstar := -7
  stages := pure 0
  Mθ _ := 0
  aθ _ _ := 0
  admissible _ _ := False
  δo := 0
  kfin := -1
  uPrim _ _ := 1
  uTilde F _ := Central.eta F.Q (fun _ => vThree) (fun _ => (1 : KPS)) * (eThree * eThree)

/-- **Non-vacuity of the tightened leaf at an unused prime** (PROVED). -/
theorem nonempty_trianglesG_three : Nonempty (CommonCoordinateTrianglesG exDataThree famThree 0) :=
  ⟨trianglesG_three exDataThree rfl rfl⟩

end ZInQ.Manuscript.RC.Wiring

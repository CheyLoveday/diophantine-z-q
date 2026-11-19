import ZInQKernel.Contrib.CloudB3RC53.Torsion.ConeCoord
import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.FullConditionE1a
import ZInQKernel.Contrib.RC53Assist.CoordProvenance.HomotopyComparison

/-!
# Independent determinant of an explicit graded comparison cone

An invertible degreewise comparison has an explicit cone contraction.  Two
unitriangular matrix operations compute its determinant as the parity sign
times the odd comparison determinant divided by the even one.  The proof
uses neither source nor target coordinates, their nonvanishing, nor an assumed
cone-normalization equality.  It therefore also applies to zero coordinates.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant

open Matrix
open ZInQ.Contrib.CloudB3RC53.Torsion

variable {K : Type} [Field K]

section MatrixCalculation

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Exchange of two equally sized blocks has the computed parity determinant. -/
theorem det_block_swap :
    (fromBlocks (0 : Matrix ι ι K) (1 : Matrix ι ι K) (1 : Matrix ι ι K) 0).det =
      (-1 : K) ^ Fintype.card ι := by
  let U : Matrix (ι ⊕ ι) (ι ⊕ ι) K := fromBlocks 1 (-1) 0 1
  let L : Matrix (ι ⊕ ι) (ι ⊕ ι) K := fromBlocks 1 0 1 1
  let V : Matrix (ι ⊕ ι) (ι ⊕ ι) K := fromBlocks 1 0 0 (-1)
  have he : U * L * U * V = fromBlocks 0 1 1 0 := by
    simp [U, L, V, fromBlocks_multiply]
  rw [← he, det_mul, det_mul, det_mul]
  simp [U, L, V, det_neg]

/-- Determinant of the actual off-diagonal cone matrix. -/
theorem det_cross (A B : Matrix ι ι K) :
    (fromBlocks 0 A B 0).det = (-1 : K) ^ Fintype.card ι * A.det * B.det := by
  have he : fromBlocks A 0 0 B * fromBlocks (0 : Matrix ι ι K) 1 1 0 = fromBlocks 0 A B 0 := by
    rw [fromBlocks_multiply]
    simp
  rw [← he, det_mul, det_fromBlocks_zero₂₁, det_block_swap]
  ring

end MatrixCalculation

section BasedComparison

variable {κe κo : Type} [Fintype κe] [Fintype κo] [DecidableEq κe] [DecidableEq κo]
  {C D : BasedCx K κe κo}

/-- Fixed degreewise inverse matrices and the actual two chain-map identities. -/
structure BasedIso (C D : BasedCx K κe κo) where
  f : ChainMapB C D
  g : ChainMapB D C
  fgE : f.fE * g.fE = 1
  fgO : f.fO * g.fO = 1
  gfE : g.fE * f.fE = 1
  gfO : g.fO * f.fO = 1

/-- The contraction of the same explicit comparison cone. -/
def BasedIso.coneContraction (I : BasedIso C D) : Contraction (BasedCx.cone I.f) where
  hOE := fromBlocks 0 0 I.g.fE 0
  hEO := fromBlocks 0 0 I.g.fO 0
  deg_hOE := by
    rintro (i | i) (j | j) h
    · exact absurd rfl h
    · exact absurd rfl h
    · have he := I.g.deg_fE i j h
      change C.degE i + -1 = D.degE j + -1
      simpa only [add_zero] using congrArg (· + -1) he
    · exact absurd rfl h
  deg_hEO := by
    rintro (i | i) (j | j) h
    · exact absurd rfl h
    · exact absurd rfl h
    · have he := I.g.deg_fO i j h
      change C.degO i + -1 = D.degO j + -1
      simpa only [add_zero] using congrArg (· + -1) he
    · exact absurd rfl h
  htpy_E := by
    change fromBlocks D.dEO I.f.fE 0 (-C.dOE) * fromBlocks 0 0 I.g.fE 0 +
      fromBlocks 0 0 I.g.fO 0 * fromBlocks D.dOE I.f.fO 0 (-C.dEO) = 1
    rw [fromBlocks_multiply, fromBlocks_multiply, fromBlocks_add]
    simp [I.fgE, I.gfO, Matrix.neg_mul, I.g.commOE, ← fromBlocks_one]
  htpy_O := by
    change fromBlocks D.dOE I.f.fO 0 (-C.dEO) * fromBlocks 0 0 I.g.fO 0 +
      fromBlocks 0 0 I.g.fE 0 * fromBlocks D.dEO I.f.fE 0 (-C.dOE) = 1
    rw [fromBlocks_multiply, fromBlocks_multiply, fromBlocks_add]
    simp [I.fgO, I.gfE, Matrix.neg_mul, I.g.commEO, ← fromBlocks_one]

/-- The oriented cross-block determinant has the actual source parity sign. -/
theorem det_oriented_cross (A : Matrix κo κo K) (B : Matrix κe κe K) (σ : κe ≃ κo) :
    ((fromBlocks 0 A B 0).submatrix (σ.sumCongr σ.symm) id).det =
      (-1 : K) ^ Fintype.card κo * A.det * B.det := by
  let e : κe ⊕ κe ≃ κe ⊕ κo := (Equiv.refl κe).sumCongr σ
  have he : ((fromBlocks (0 : Matrix κo κe K) A B 0).submatrix (σ.sumCongr σ.symm) id).submatrix e e =
      fromBlocks 0 (A.submatrix σ σ) B 0 := by
    ext (i | i) (j | j) <;> simp [e]
  rw [← det_submatrix_equiv_self e, he, det_cross, det_submatrix_equiv_self,
    Fintype.card_congr σ]

/-- Unitriangular operations compute the cone determinant independently of coordinates. -/
theorem BasedIso.coneMatrix_det (I : BasedIso C D) (σ : κe ≃ κo) :
    ((fromBlocks D.dOE I.f.fO I.g.fE (-C.dEO)).submatrix (σ.sumCongr σ.symm) id).det =
      (-1 : K) ^ Fintype.card κo * I.f.fO.det * I.g.fE.det := by
  let M : Matrix (κo ⊕ κe) (κe ⊕ κo) K := fromBlocks D.dOE I.f.fO I.g.fE (-C.dEO)
  let U : Matrix (κe ⊕ κo) (κe ⊕ κo) K := fromBlocks 1 (I.f.fE * C.dEO) 0 1
  let L : Matrix (κo ⊕ κe) (κo ⊕ κe) K := fromBlocks 1 (-(D.dOE * I.f.fE)) 0 1
  have hu : M * U = fromBlocks D.dOE I.f.fO I.g.fE 0 := by
    rw [show M = fromBlocks D.dOE I.f.fO I.g.fE (-C.dEO) from rfl,
      show U = fromBlocks 1 (I.f.fE * C.dEO) 0 1 from rfl, fromBlocks_multiply]
    have htop : D.dOE * (I.f.fE * C.dEO) = 0 := by
      rw [← Matrix.mul_assoc, I.f.commOE, Matrix.mul_assoc, C.dd_O, Matrix.mul_zero]
    have hbot : I.g.fE * (I.f.fE * C.dEO) = C.dEO := by
      rw [← Matrix.mul_assoc, I.gfE, Matrix.one_mul]
    simp [htop, hbot]
  have hl : L * M * U = fromBlocks 0 I.f.fO I.g.fE 0 := by
    rw [Matrix.mul_assoc, hu]
    change fromBlocks 1 (-(D.dOE * I.f.fE)) 0 1 * fromBlocks D.dOE I.f.fO I.g.fE 0 = _
    rw [fromBlocks_multiply]
    have htop : -(D.dOE * I.f.fE) * I.g.fE = -D.dOE := by
      rw [Matrix.neg_mul, Matrix.mul_assoc, I.fgE, Matrix.mul_one]
    simp [htop]
  have hU : U.det = 1 := by simp [U]
  have hL : L.det = 1 := by simp [L]
  let τ : κe ⊕ κo ≃ κo ⊕ κe := σ.sumCongr σ.symm
  have hdet : ((L * M * U).submatrix τ id).det = (M.submatrix τ id).det := by
    rw [Matrix.submatrix_mul _ _ τ id id Function.bijective_id,
      Matrix.submatrix_mul _ _ τ τ id τ.bijective, submatrix_id_id,
      det_mul, det_mul, det_submatrix_equiv_self, hL, hU, one_mul, mul_one]
  rw [hl] at hdet
  exact hdet.symm.trans (det_oriented_cross I.f.fO I.g.fE σ)

/-- The independently computed cone torsion.  No coordinate equality or
nonzero source/target coordinate is an input. -/
theorem BasedIso.cone_torsion (I : BasedIso C D) (σ : κe ≃ κo) :
    torsion (BasedCx.cone I.f) (σ.sumCongr σ.symm) =
      (-1 : K) ^ Fintype.card κo * I.f.fO.det * I.g.fE.det := by
  rw [← tau_eq_torsion _ I.coneContraction]
  unfold tau
  have he : (BasedCx.cone I.f).dOE + I.coneContraction.hOE =
      fromBlocks D.dOE I.f.fO I.g.fE (-C.dEO) := by
    change fromBlocks D.dOE I.f.fO 0 (-C.dEO) + fromBlocks 0 0 I.g.fE 0 = _
    rw [fromBlocks_add]
    simp
  rw [he]
  exact I.coneMatrix_det σ

end BasedComparison

section ExplicitBasis

variable {κe κo : Type} [Fintype κe] [Fintype κo] [DecidableEq κe] [DecidableEq κo]
  (C : BasedCx K κe κo)

/-- The forward chain map is the displayed graded basis matrix. -/
def basisForward (P : GradedBasisChange C) : ChainMapB C (C.rebase P) where
  fE := P.Pe
  fO := P.Po
  deg_fE := P.deg_Pe
  deg_fO := P.deg_Po
  commOE := by
    change P.Po * C.dOE * P.Qe * P.Pe = P.Po * C.dOE
    rw [Matrix.mul_assoc, mul_eq_one_comm.mp P.hPQe, Matrix.mul_one]
  commEO := by
    change P.Pe * C.dEO * P.Qo * P.Po = P.Pe * C.dEO
    rw [Matrix.mul_assoc, mul_eq_one_comm.mp P.hPQo, Matrix.mul_one]

/-- The inverse chain map uses the fixed inverse basis matrices. -/
def basisBackward (P : GradedBasisChange C) : ChainMapB (C.rebase P) C where
  fE := P.Qe
  fO := P.Qo
  deg_fE := P.deg_Qe
  deg_fO := P.deg_Qo
  commOE := by
    change C.dOE * P.Qe = P.Qo * (P.Po * C.dOE * P.Qe)
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_eq_one_comm.mp P.hPQo, Matrix.one_mul]
  commEO := by
    change C.dEO * P.Qo = P.Qe * (P.Pe * C.dEO * P.Qo)
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_eq_one_comm.mp P.hPQe, Matrix.one_mul]

def basisIso (P : GradedBasisChange C) : BasedIso C (C.rebase P) where
  f := basisForward C P
  g := basisBackward C P
  fgE := P.hPQe
  fgO := P.hPQo
  gfE := mul_eq_one_comm.mp P.hPQe
  gfO := mul_eq_one_comm.mp P.hPQo

/-- Actual graded basis matrices supply their cone determinant independently. -/
theorem basis_cone_torsion (P : GradedBasisChange C) (σ : κe ≃ κo) :
    torsion (BasedCx.cone (basisForward C P)) (σ.sumCongr σ.symm) =
      (-1 : K) ^ Fintype.card κo * P.Po.det * P.Qe.det :=
  (basisIso C P).cone_torsion σ

end ExplicitBasis

section SplitProjection

open ZInQ.Contrib.CloudB3RC53.ClearingComplex

variable {κe κo ν : Type} [Fintype κe] [Fintype κo] [Fintype ν]
  [DecidableEq κe] [DecidableEq κo] [DecidableEq ν]
  (D : BasedCx K κe κo) (B : Matrix ν ν K)

/-- The fixed singular disk is in degrees one and two. -/
abbrev oddMatrixDisk : BasedCx K ν ν := shiftCx (diskM 0 (by decide) B) 1 (by decide)

def basedIdentity : ChainMapB D D where
  fE := 1
  fO := 1
  deg_fE := hasDeg_one _
  deg_fO := hasDeg_one _
  commOE := by rw [Matrix.mul_one, Matrix.one_mul]
  commEO := by rw [Matrix.mul_one, Matrix.one_mul]

def identityIso : BasedIso D D where
  f := basedIdentity D
  g := basedIdentity D
  fgE := Matrix.one_mul _
  fgO := Matrix.one_mul _
  gfE := Matrix.one_mul _
  gfO := Matrix.one_mul _

/-- Projection after the displayed singular disk has been split from the
retained complex.  Its cone uses those fixed matrices, not coordinate equality. -/
def splitProjection : ChainMapB (D.sum (oddMatrixDisk B)) D where
  fE := fromCols 1 0
  fO := fromCols 1 0
  deg_fE := by
    rintro i (j | j) h
    · change D.degE i = D.degE j + 0
      exact hasDeg_one D.degE i j h
    · exact absurd rfl h
  deg_fO := by
    rintro i (j | j) h
    · change D.degO i = D.degO j + 0
      exact hasDeg_one D.degO i j h
    · exact absurd rfl h
  commOE := by
    change D.dOE * fromCols 1 0 = fromCols 1 0 * fromBlocks D.dOE 0 0 0
    rw [mul_fromCols, fromCols_mul_fromBlocks]
    simp
  commEO := by
    change D.dEO * fromCols 1 0 = fromCols 1 0 * fromBlocks D.dEO 0 0 B
    rw [mul_fromCols, fromCols_mul_fromBlocks]
    simp

/-- Regrouping the actual projection cone separates its identity cone and the
shifted singular disk with differential -B. -/
theorem splitProjection_cone_reindex :
    (BasedCx.cone (splitProjection D B)).reindex (Equiv.sumAssoc κe κo ν).symm
      (Equiv.sumAssoc κo κe ν).symm =
      (BasedCx.cone (basedIdentity D)).sum (diskM 0 (by decide) (-B)) := by
  apply BasedCx.ext'
  · funext i
    rcases i with (i | i) | i <;> simp [BasedCx.reindex, BasedCx.cone, BasedCx.sum,
      oddMatrixDisk, shiftCx, diskM]
  · funext i
    rcases i with (i | i) | i <;> simp [BasedCx.reindex, BasedCx.cone, BasedCx.sum,
      oddMatrixDisk, shiftCx, diskM]
  · ext i j
    rcases i with (i | i) | i <;> rcases j with (j | j) | j <;>
      simp [BasedCx.reindex, BasedCx.cone, BasedCx.sum, splitProjection, basedIdentity,
        oddMatrixDisk, shiftCx, diskM]
  · ext i j
    rcases i with (i | i) | i <;> rcases j with (j | j) | j <;>
      simp [BasedCx.reindex, BasedCx.cone, BasedCx.sum, splitProjection, basedIdentity,
        oddMatrixDisk, shiftCx, diskM]

omit [Fintype κe] [Fintype κo] [Fintype ν] [DecidableEq κe] [DecidableEq κo] [DecidableEq ν] in
/-- The fixed cone orientation is regrouped, not adjusted to force equality. -/
theorem splitProjection_orientation (σ : κe ≃ κo) :
    (Equiv.sumAssoc κe κo ν).trans
      ((σ.sumCongr (σ.sumCongr (Equiv.refl ν)).symm).trans (Equiv.sumAssoc κo κe ν).symm) =
      (σ.sumCongr σ.symm).sumCongr (Equiv.refl ν) := by
  ext i
  rcases i with (i | i) | i <;> rfl

/-- The independent cone-basis determinant of the singular-disk projection.
This includes nonacyclic retained complexes and zero augmented coordinates. -/
theorem splitProjection_cone_torsion (hB : IsUnit B.det) (σ : κe ≃ κo) :
    torsion (BasedCx.cone (splitProjection D B))
      (σ.sumCongr (σ.sumCongr (Equiv.refl ν)).symm) =
      (-1 : K) ^ Fintype.card (κo ⊕ ν) * B.det := by
  have hnB : IsUnit (-B).det := by
    rw [det_neg]
    exact (isUnit_neg_one.pow _).mul hB
  have hr := torsion_reindex' (BasedCx.cone (splitProjection D B))
    (σ.sumCongr (σ.sumCongr (Equiv.refl ν)).symm)
    (Equiv.sumAssoc κe κo ν).symm (Equiv.sumAssoc κo κe ν).symm
  rw [splitProjection_cone_reindex, Equiv.symm_symm, splitProjection_orientation] at hr
  let hId : Contraction (BasedCx.cone (basedIdentity D)) := (identityIso D).coneContraction
  have hsum := torsion_sum (BasedCx.cone (basedIdentity D)) (diskM 0 (by decide) (-B)) hId
    (diskMContraction 0 (by decide) (-B) hnB) (σ.sumCongr σ.symm) (Equiv.refl ν)
  have hIdT : torsion (BasedCx.cone (basedIdentity D)) (σ.sumCongr σ.symm) =
      (-1 : K) ^ Fintype.card κo * (1 : Matrix κo κo K).det * (1 : Matrix κe κe K).det :=
    (identityIso D).cone_torsion σ
  rw [← hr, hsum, hIdT, torsion_diskM 0 (by decide) (-B) hnB, det_neg]
  rw [det_one, det_one, mul_one, mul_one, ← mul_assoc, ← pow_add, Fintype.card_sum]

end SplitProjection

section TwoTermBases

variable {n : ℕ} (D P Q : Matrix (Fin n) (Fin n) K) (hP : IsUnit P.det) (hQ : IsUnit Q.det)

/-- The exact original-to-triangular basis map of the stored two-term matrix. -/
def twoTermForward : FourMap (twoTerm D) (twoTerm (P * D * Q)) where
  f0 := 1
  f1 := Q⁻¹
  f2 := P
  f3 := 1
  c0 := by simp [twoTerm]
  c1 := by
    change P * D * Q * Q⁻¹ = P * D
    rw [Matrix.mul_assoc, mul_nonsing_inv _ hQ, Matrix.mul_one]
  c2 := by simp [twoTerm]

def twoTermBackward : FourMap (twoTerm (P * D * Q)) (twoTerm D) where
  f0 := 1
  f1 := Q
  f2 := P⁻¹
  f3 := 1
  c0 := by simp [twoTerm]
  c1 := by
    change D * Q = P⁻¹ * (P * D * Q)
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, nonsing_inv_mul _ hP, Matrix.one_mul]
  c2 := by simp [twoTerm]

variable (z w : Fin n → K) (hz : D *ᵥ z = 0) (hw : w ᵥ* D = 0)

include hQ hz in
/-- The same original cycle in the fixed target bases. -/
theorem twoTerm_target_cycle : (P * D * Q) *ᵥ (Q⁻¹ *ᵥ z) = 0 := by
  rw [mulVec_mulVec, Matrix.mul_assoc, mul_nonsing_inv _ hQ, Matrix.mul_one,
    ← mulVec_mulVec, hz, mulVec_zero]

include hP hw in
/-- The same original closed functional in the fixed target bases. -/
theorem twoTerm_target_functional : (w ᵥ* P⁻¹) ᵥ* (P * D * Q) = 0 := by
  rw [vecMul_vecMul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, nonsing_inv_mul _ hP,
    Matrix.one_mul, ← vecMul_vecMul, hw, zero_vecMul]

/-- The actual augmented maps are mutual inverses, including their two augmentation lines. -/
def twoTermAugIso : BasedIso (twoTerm D |>.aug z w hz hw |>.toBased)
    (twoTerm (P * D * Q) |>.aug (Q⁻¹ *ᵥ z) (w ᵥ* P⁻¹)
      (twoTerm_target_cycle D P Q hQ z hz) (twoTerm_target_functional D P Q hP w hw) |>.toBased) where
  f := (twoTermForward D P Q hQ).augMap z w hz hw (Q⁻¹ *ᵥ z) (w ᵥ* P⁻¹)
    (twoTerm_target_cycle D P Q hQ z hz) (twoTerm_target_functional D P Q hP w hw) rfl
    (by
      change (w ᵥ* P⁻¹) ᵥ* P = w
      rw [vecMul_vecMul, nonsing_inv_mul _ hP, vecMul_one])
  g := (twoTermBackward D P Q hP).augMap (Q⁻¹ *ᵥ z) (w ᵥ* P⁻¹)
    (twoTerm_target_cycle D P Q hQ z hz) (twoTerm_target_functional D P Q hP w hw) z w hz hw
    (by
      change Q *ᵥ (Q⁻¹ *ᵥ z) = z
      rw [mulVec_mulVec, mul_nonsing_inv _ hQ, one_mulVec]) rfl
  fgE := by
    change fromBlocks (fromBlocks 1 0 0 1) 0 0 P * fromBlocks (fromBlocks 1 0 0 1) 0 0 P⁻¹ = 1
    rw [fromBlocks_multiply, fromBlocks_multiply]
    simp [mul_nonsing_inv _ hP, ← fromBlocks_one]
  fgO := by
    change fromBlocks Q⁻¹ 0 0 (fromBlocks 1 0 0 1) * fromBlocks Q 0 0 (fromBlocks 1 0 0 1) = 1
    rw [fromBlocks_multiply, fromBlocks_multiply]
    simp [nonsing_inv_mul _ hQ, ← fromBlocks_one]
  gfE := by
    change fromBlocks (fromBlocks 1 0 0 1) 0 0 P⁻¹ * fromBlocks (fromBlocks 1 0 0 1) 0 0 P = 1
    rw [fromBlocks_multiply, fromBlocks_multiply]
    simp [nonsing_inv_mul _ hP, ← fromBlocks_one]
  gfO := by
    change fromBlocks Q 0 0 (fromBlocks 1 0 0 1) * fromBlocks Q⁻¹ 0 0 (fromBlocks 1 0 0 1) = 1
    rw [fromBlocks_multiply, fromBlocks_multiply]
    simp [mul_nonsing_inv _ hQ, ← fromBlocks_one]

/-- Independent normalization for the very same original and triangular
matrices.  In particular this is not obtained from equality of their coordinates. -/
theorem twoTerm_basis_cone_torsion :
    torsion (BasedCx.cone (twoTermAugIso D P Q hP hQ z w hz hw).f)
      ((σ₀ n).sumCongr (σ₀ n).symm) =
      (-1 : K) ^ Fintype.card (Fin n ⊕ (Empty ⊕ Unit)) * (P.det * Q.det)⁻¹ := by
  rw [(twoTermAugIso D P Q hP hQ z w hz hw).cone_torsion (σ₀ n)]
  have hdetP : (P⁻¹).det = P.det⁻¹ := by
    rw [det_nonsing_inv]
    exact eq_inv_of_mul_eq_one_left (Ring.inverse_mul_cancel _ hP)
  have hdetQ : (Q⁻¹).det = Q.det⁻¹ := by
    rw [det_nonsing_inv]
    exact eq_inv_of_mul_eq_one_left (Ring.inverse_mul_cancel _ hQ)
  change (-1 : K) ^ Fintype.card (Fin n ⊕ (Empty ⊕ Unit)) *
    (fromBlocks Q⁻¹ 0 0 (fromBlocks (1 : Matrix Empty Empty K) 0 0 1)).det *
    (fromBlocks (fromBlocks (1 : Matrix Empty Empty K) 0 0 1) 0 0 P⁻¹).det = _
  simp only [det_fromBlocks_zero₂₁, det_one, mul_one, one_mul, hdetP, hdetQ]
  rw [mul_inv]
  ring

/-- The transport factor is computed from P and Q for zero and nonzero
coordinates alike.  No torsion-normalization or coordinate-equality premise is used. -/
theorem twoTerm_basis_factor :
    (-1 : K) ^ Fintype.card (Fin n ⊕ (Empty ⊕ Unit)) *
      (torsion (BasedCx.cone (twoTermAugIso D P Q hP hQ z w hz hw).f)
        ((σ₀ n).sumCongr (σ₀ n).symm))⁻¹ = P.det * Q.det := by
  rw [twoTerm_basis_cone_torsion, mul_inv, inv_inv]
  have hs : (-1 : K) ^ Fintype.card (Fin n ⊕ (Empty ⊕ Unit)) ≠ 0 :=
    pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul]

end TwoTermBases

section SourceBasis

variable {κe κo κe' κo' : Type}
  [Fintype κe] [Fintype κo] [Fintype κe'] [Fintype κo']
  [DecidableEq κe] [DecidableEq κo] [DecidableEq κe'] [DecidableEq κo']
  {C C' : BasedCx K κe κo} {D : BasedCx K κe' κo'}

def transportSource (h : C = C') (f : ChainMapB C' D) : ChainMapB C D where
  fE := f.fE
  fO := f.fO
  deg_fE := by cases h; exact f.deg_fE
  deg_fO := by cases h; exact f.deg_fO
  commOE := by cases h; exact f.commOE
  commEO := by cases h; exact f.commEO

theorem transportSource_cone (h : C = C') (f : ChainMapB C' D)
    (σD : κe' ≃ κo') (σC : κe ≃ κo) :
    torsion (BasedCx.cone (transportSource h f)) (σD.sumCongr σC.symm) =
      torsion (BasedCx.cone f) (σD.sumCongr σC.symm) := by
  cases h
  rfl

omit [DecidableEq κe] [DecidableEq κo] [DecidableEq κe'] [DecidableEq κo'] in
theorem chainMap_ext {f g : ChainMapB C D} (hE : f.fE = g.fE) (hO : f.fO = g.fO) : f = g := by
  cases f
  cases g
  cases hE
  cases hO
  rfl

def chainComp {κe'' κo'' : Type} [Fintype κe''] [Fintype κo'']
    [DecidableEq κe''] [DecidableEq κo''] {T : BasedCx K κe'' κo''}
    (f : ChainMapB C D) (g : ChainMapB D T) : ChainMapB C T where
  fE := g.fE * f.fE
  fO := g.fO * f.fO
  deg_fE := by simpa using g.deg_fE.mul f.deg_fE
  deg_fO := by simpa using g.deg_fO.mul f.deg_fO
  commOE := by
    rw [← Matrix.mul_assoc, g.commOE, Matrix.mul_assoc, f.commOE, ← Matrix.mul_assoc]
  commEO := by
    rw [← Matrix.mul_assoc, g.commEO, Matrix.mul_assoc, f.commEO, ← Matrix.mul_assoc]

/-- Rebase the source of the fixed map, preserving its literal inverse-basis matrices. -/
def sourceRebased (f : ChainMapB C D) (P : GradedBasisChange C) : ChainMapB (C.rebase P) D where
  fE := f.fE * P.Qe
  fO := f.fO * P.Qo
  deg_fE := by
    change HasDeg (f.fE * P.Qe) D.degE C.degE 0
    simpa using f.deg_fE.mul P.deg_Qe
  deg_fO := by
    change HasDeg (f.fO * P.Qo) D.degO C.degO 0
    simpa using f.deg_fO.mul P.deg_Qo
  commOE := by
    change D.dOE * (f.fE * P.Qe) = f.fO * P.Qo * (P.Po * C.dOE * P.Qe)
    rw [← Matrix.mul_assoc, f.commOE]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P.Qo, mul_eq_one_comm.mp P.hPQo, Matrix.one_mul]
  commEO := by
    change D.dEO * (f.fO * P.Qo) = f.fE * P.Qe * (P.Pe * C.dEO * P.Qo)
    rw [← Matrix.mul_assoc, f.commEO]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P.Qe, mul_eq_one_comm.mp P.hPQe, Matrix.one_mul]

/-- The cone basis uses the opposite parity of the rebased source. -/
def sourceConeBasis (f : ChainMapB C D) (P : GradedBasisChange C) :
    GradedBasisChange (BasedCx.cone f) where
  Pe := fromBlocks 1 0 0 P.Po
  Qe := fromBlocks 1 0 0 P.Qo
  Po := fromBlocks 1 0 0 P.Pe
  Qo := fromBlocks 1 0 0 P.Qe
  hPQe := by rw [fromBlocks_multiply]; simp [P.hPQo, ← fromBlocks_one]
  hPQo := by rw [fromBlocks_multiply]; simp [P.hPQe, ← fromBlocks_one]
  deg_Pe := by
    rintro (i | i) (j | j) h
    · exact hasDeg_one _ i j h
    · exact absurd rfl h
    · exact absurd rfl h
    · change C.degO i + -1 = C.degO j + -1 + 0
      simpa only [add_zero] using congrArg (· + -1) (P.deg_Po i j h)
  deg_Qe := by
    rintro (i | i) (j | j) h
    · exact hasDeg_one _ i j h
    · exact absurd rfl h
    · exact absurd rfl h
    · change C.degO i + -1 = C.degO j + -1 + 0
      simpa only [add_zero] using congrArg (· + -1) (P.deg_Qo i j h)
  deg_Po := by
    rintro (i | i) (j | j) h
    · exact hasDeg_one _ i j h
    · exact absurd rfl h
    · exact absurd rfl h
    · change C.degE i + -1 = C.degE j + -1 + 0
      simpa only [add_zero] using congrArg (· + -1) (P.deg_Pe i j h)
  deg_Qo := by
    rintro (i | i) (j | j) h
    · exact hasDeg_one _ i j h
    · exact absurd rfl h
    · exact absurd rfl h
    · change C.degE i + -1 = C.degE j + -1 + 0
      simpa only [add_zero] using congrArg (· + -1) (P.deg_Qe i j h)

theorem sourceConeBasis_rebase (f : ChainMapB C D) (P : GradedBasisChange C) :
    (BasedCx.cone f).rebase (sourceConeBasis f P) = BasedCx.cone (sourceRebased f P) := by
  apply BasedCx.ext'
  · rfl
  · rfl
  · change fromBlocks 1 0 0 P.Pe * fromBlocks D.dOE f.fO 0 (-C.dEO) *
      fromBlocks 1 0 0 P.Qo = fromBlocks D.dOE (f.fO * P.Qo) 0 (-(P.Pe * C.dEO * P.Qo))
    rw [fromBlocks_multiply, fromBlocks_multiply]
    simp [Matrix.mul_neg, Matrix.neg_mul]
  · change fromBlocks 1 0 0 P.Po * fromBlocks D.dEO f.fE 0 (-C.dOE) *
      fromBlocks 1 0 0 P.Qe = fromBlocks D.dEO (f.fE * P.Qe) 0 (-(P.Po * C.dOE * P.Qe))
    rw [fromBlocks_multiply, fromBlocks_multiply]
    simp [Matrix.mul_neg, Matrix.neg_mul]

/-- The actual source-basis contribution to the cone determinant is computed
from its displayed matrices, not inferred from the coordinate comparison. -/
theorem source_basis_cone_torsion (f : ChainMapB C D) (P : GradedBasisChange C)
    (σD : κe' ≃ κo') (σC : κe ≃ κo) :
    torsion (BasedCx.cone (sourceRebased f P)) (σD.sumCongr σC.symm) =
      P.Pe.det * torsion (BasedCx.cone f) (σD.sumCongr σC.symm) * P.Qo.det := by
  have h := torsion_rebase' (BasedCx.cone f) (sourceConeBasis f P) (σD.sumCongr σC.symm)
  rw [sourceConeBasis_rebase] at h
  simpa only [sourceConeBasis, det_fromBlocks_zero₂₁, det_one, one_mul] using h

end SourceBasis

section RebasedProjection

variable {κe κo ν : Type} [Fintype κe] [Fintype κo] [Fintype ν]
  [DecidableEq κe] [DecidableEq κo] [DecidableEq ν]
  (C : BasedCx K (κe ⊕ ν) (κo ⊕ ν)) (D : BasedCx K κe κo) (B : Matrix ν ν K)
  (P : GradedBasisChange C) (hsplit : C.rebase P = D.sum (oddMatrixDisk B))

/-- The map is fixed by the displayed split and original basis matrices. -/
def rebasedProjection : ChainMapB C D :=
  chainComp (basisForward C P) (transportSource hsplit (splitProjection D B))

theorem rebasedProjection_source :
    sourceRebased (rebasedProjection C D B P hsplit) P = transportSource hsplit (splitProjection D B) := by
  apply chainMap_ext
  · change (fromCols 1 0 * P.Pe) * P.Qe = fromCols 1 0
    rw [Matrix.mul_assoc, P.hPQe, Matrix.mul_one]
  · change (fromCols 1 0 * P.Po) * P.Qo = fromCols 1 0
    rw [Matrix.mul_assoc, P.hPQo, Matrix.mul_one]

/-- Only actual elementary matrix determinants, not a cone-basis equality,
are needed to transport the independently calculated projection determinant. -/
theorem rebasedProjection_cone_torsion (hB : IsUnit B.det)
    (hPe : P.Pe.det = 1) (hQo : P.Qo.det = 1) (σ : κe ≃ κo) :
    torsion (BasedCx.cone (rebasedProjection C D B P hsplit))
      (σ.sumCongr (σ.sumCongr (Equiv.refl ν)).symm) =
      (-1 : K) ^ Fintype.card (κo ⊕ ν) * B.det := by
  have h := source_basis_cone_torsion (rebasedProjection C D B P hsplit) P σ
    (σ.sumCongr (Equiv.refl ν))
  rw [rebasedProjection_source, transportSource_cone, hPe, hQo, one_mul, mul_one] at h
  exact h.symm.trans (splitProjection_cone_torsion D B hB σ)

end RebasedProjection

section NativeSingularCancellation

open ZInQ.Contrib.CloudB3RC53.ClearingComplex

variable {α β ν : Type} [Fintype α] [Fintype β] [Fintype ν]
  [DecidableEq α] [DecidableEq β] [DecidableEq ν]
  (C : BasedCx K (α ⊕ ν) (β ⊕ ν))
  (ho : ∀ v, C.degO (Sum.inr v) = 1) (he : ∀ v, C.degE (Sum.inr v) = 2)
  (hB : IsUnit C.dEO.toBlocks₂₂.det)

/-- The actual odd cancellation uses the two fixed elementary matrices. -/
def oddCancelBasis : GradedBasisChange C := by
  let P := cancelBasis (C := shiftCx C 1 odd_one) 2 (shift_degE C 1 ho) (shift_degO C 1 he)
  refine
    { Pe := P.Po
      Qe := P.Qo
      Po := P.Pe
      Qo := P.Qe
      hPQe := P.hPQo
      hPQo := P.hPQe
      deg_Pe := ?_
      deg_Qe := ?_
      deg_Po := ?_
      deg_Qo := ?_ }
  · intro i j h
    have hh := P.deg_Po i j h
    change C.degE i + 1 = C.degE j + 1 + 0 at hh
    change C.degE i = C.degE j + 0
    omega
  · intro i j h
    have hh := P.deg_Qo i j h
    change C.degE i + 1 = C.degE j + 1 + 0 at hh
    change C.degE i = C.degE j + 0
    omega
  · intro i j h
    have hh := P.deg_Pe i j h
    change C.degO i + 1 = C.degO j + 1 + 0 at hh
    change C.degO i = C.degO j + 0
    omega
  · intro i j h
    have hh := P.deg_Qe i j h
    change C.degO i + 1 = C.degO j + 1 + 0 at hh
    change C.degO i = C.degO j + 0
    omega

theorem oddCancelBasis_even_det : (oddCancelBasis C ho he).Pe.det = 1 := by
  change (fromBlocks 1 (-(C.dEO.toBlocks₁₂ * C.dEO.toBlocks₂₂⁻¹)) 0 1).det = 1
  simp

theorem oddCancelBasis_inverse_odd_det : (oddCancelBasis C ho he).Qo.det = 1 := by
  change (fromBlocks 1 0 (-(C.dEO.toBlocks₂₂⁻¹ * C.dEO.toBlocks₂₁)) 1).det = 1
  simp

/-- The splitting equation is derived from the actual differential blocks and d²=0. -/
theorem oddCancelBasis_split :
    C.rebase (oddCancelBasis C ho he) = (schurO C 1 ho he hB).sum (oddMatrixDisk C.dEO.toBlocks₂₂) := by
  have h := rebase_eq (C := shiftCx C 1 odd_one) 2 (shift_degE C 1 ho)
    (shift_degO C 1 he) hB (by decide)
  apply BasedCx.ext'
  · funext i
    cases i with
    | inl i => change C.degE (Sum.inl i) = C.degE (Sum.inl i) + 1 + -1; omega
    | inr i => change C.degE (Sum.inr i) = 2; exact he i
  · funext i
    cases i with
    | inl i => change C.degO (Sum.inl i) = C.degO (Sum.inl i) + 1 + -1; omega
    | inr i => change C.degO (Sum.inr i) = 1; exact ho i
  · exact congrArg BasedCx.dEO h
  · exact congrArg BasedCx.dOE h

end NativeSingularCancellation

section FullModelCone

open ZInQ.Contrib.CloudB3RC53.ClearingComplex

variable {C : FullPreComplex K} (hB : IsUnit C.B.det)
  (z : C.D1 ⊕ C.N → K) (lam : C.D2 ⊕ C.N → K)
  (hz : C.toFour.d1 *ᵥ z = 0) (hlam : lam ᵥ* C.toFour.d1 = 0)

local instance fullD1Decidable : DecidableEq C.D1 := inferInstance
local instance fullD2Decidable : DecidableEq C.D2 := inferInstance
local instance fullNDecidable : DecidableEq C.N := C.dN

/-- The actual retained cancellation target is the native augmented remaining complex. -/
abbrev fullRemaining : BasedCx K ((Fin C.m0 ⊕ Unit) ⊕ C.D2) (C.D1 ⊕ (Fin C.m2 ⊕ Unit)) :=
  ((C.cancel hB).toFour.aug (z ∘ Sum.inl) (lam ∘ Sum.inl)
    (FullPreComplex.hz_full hB hz) (FullPreComplex.hlam_full hB hlam)).toBased

theorem full_actual_split :
    (Xf z lam hz hlam).rebase (oddCancelBasis (Xf z lam hz hlam)
      (Xf_degO z lam hz hlam) (Xf_degE z lam hz hlam)) =
      (fullRemaining hB z lam hz hlam).sum (oddMatrixDisk C.B) := by
  have h := oddCancelBasis_split (Xf z lam hz hlam) (Xf_degO z lam hz hlam)
    (Xf_degE z lam hz hlam) (Xf_hA hB)
  rw [schurO_Xf hB, Xf_blk] at h
  exact h

/-- The comparison uses the actual native matrices and actual retained class
and functional.  There is no coordinate-equality or normalization parameter. -/
def actualFullProjection : ChainMapB (Xf z lam hz hlam) (fullRemaining hB z lam hz hlam) :=
  rebasedProjection (Xf z lam hz hlam) (fullRemaining hB z lam hz hlam) C.B
    (oddCancelBasis (Xf z lam hz hlam) (Xf_degO z lam hz hlam) (Xf_degE z lam hz hlam))
    (full_actual_split hB z lam hz hlam)

/-- Independent cone-basis determinant of the actual full-condition singular
cancellation, in the native retained orientation after the fixed relabelling.
The remaining factor for any further stored-endpoint comparison is separate. -/
theorem actualFullProjection_cone_torsion :
    torsion (BasedCx.cone (actualFullProjection hB z lam hz hlam))
      ((σBlock C.m0 C.m1 C.m2).sumCongr
        ((σBlock C.m0 C.m1 C.m2).sumCongr (Equiv.refl C.N)).symm) =
      (-1 : K) ^ Fintype.card ((C.D1 ⊕ (Fin C.m2 ⊕ Unit)) ⊕ C.N) * C.B.det :=
  rebasedProjection_cone_torsion (Xf z lam hz hlam) (fullRemaining hB z lam hz hlam) C.B
    (oddCancelBasis (Xf z lam hz hlam) (Xf_degO z lam hz hlam) (Xf_degE z lam hz hlam))
    (full_actual_split hB z lam hz hlam) hB
    (oddCancelBasis_even_det (Xf z lam hz hlam) (Xf_degO z lam hz hlam) (Xf_degE z lam hz hlam))
    (oddCancelBasis_inverse_odd_det (Xf z lam hz hlam) (Xf_degO z lam hz hlam) (Xf_degE z lam hz hlam))
    (σBlock C.m0 C.m1 C.m2)

/-- Literal readback of the actual even projection matrix after the fixed
full-condition relabelling and Schur shear. -/
theorem actualFullProjection_even_matrix :
    (actualFullProjection hB z lam hz hlam).fE =
      fromCols 1 (-((Xf z lam hz hlam).dEO.toBlocks₁₂ * C.B⁻¹)) := by
  change fromCols 1 0 * fromBlocks 1
    (-((Xf z lam hz hlam).dEO.toBlocks₁₂ * (Xf z lam hz hlam).dEO.toBlocks₂₂⁻¹)) 0 1 = _
  rw [fromCols_mul_fromBlocks, Xf_blk]
  simp

/-- Literal readback of the actual odd projection matrix. -/
theorem actualFullProjection_odd_matrix : (actualFullProjection hB z lam hz hlam).fO = fromCols 1 0 := by
  change fromCols 1 0 * fromBlocks 1 0
    ((Xf z lam hz hlam).dEO.toBlocks₂₂⁻¹ * (Xf z lam hz hlam).dEO.toBlocks₂₁) 1 = _
  rw [fromCols_mul_fromBlocks]
  simp

/-- The actual singular cancellation factor is det(B)⁻¹, independently
calculated.  It is not silently set to one on a nonzero-coordinate branch. -/
theorem actualFullProjection_factor :
    (-1 : K) ^ Fintype.card ((C.D1 ⊕ (Fin C.m2 ⊕ Unit)) ⊕ C.N) *
      (torsion (BasedCx.cone (actualFullProjection hB z lam hz hlam))
        ((σBlock C.m0 C.m1 C.m2).sumCongr
          ((σBlock C.m0 C.m1 C.m2).sumCongr (Equiv.refl C.N)).symm))⁻¹ = C.B.det⁻¹ := by
  rw [actualFullProjection_cone_torsion, mul_inv]
  have hs : (-1 : K) ^ Fintype.card ((C.D1 ⊕ (Fin C.m2 ⊕ Unit)) ⊕ C.N) ≠ 0 :=
    pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul]

end FullModelCone

end ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant

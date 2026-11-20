import ZInQKernel.Contrib.CloudB3RC53.Torsion.KummerIdentification

/-!
# Matrix torsion disks for the Knudsen–Mumford coordinate (Lane RC35)

The integral central model of the calibration has *matrix* torsion disks `B₁` (degrees `0 → 1`),
`B₂` (`1 → 2`), `B₃` (`2 → 3`) with unit determinant, while the Kummer model `kummerModel` of the
torsion library has *scalar* disks. This file shows that the Knudsen–Mumford coordinate only sees
the determinants: a disk with cokernel in degree `i` contributes `(det B_i)^{(−1)^{i+1}}`
(tex L4057–4060).

* `diskMat01`, `diskMat12`, `diskMat23`: the matrix disks; `diskMat01Contraction`, … (via `B⁻¹`).
* `torsion_diskMat01`, `torsion_diskMat12`, `torsion_diskMat23`: torsions `det B`, `(det B)⁻¹`,
  `det B` (no orientation sign).
* `kummerModelMat`, `kzM`, `kwM`, `σKM`, `kmCoord_kummerModelMat`: the core plus matrix disks has
  coordinate `u · det B₁ · (det B₂)⁻¹ · det B₃`.
* `kmCoord_kummerModelMat_eq_scalar`: it equals the coordinate of the scalar Kummer model with the
  determinant disks.
* `kmCoord_add_boundary_class`, `kmCoord_add_boundary_functional`: over a domain the coordinate
  of any four-term complex is unchanged when the class changes by a boundary `d⁰ x` or the
  functional by a coboundary `μ d²`.
* `kmCoord_kummerModelMat_example`: non-vacuity over `ℚ`.

**Classification.** PROVED.
-/

namespace ZInQ.Manuscript.RC.Wiring.KmIdent

open ZInQ.Contrib.CloudB3RC53.Torsion Matrix

variable {R : Type*} [CommRing R]

/-! ### Matrix disks -/

section Disks

variable {m : ℕ}

/-- The matrix disk with cokernel in degree one: `C⁰ = R^m --B--> R^m = C¹`. (definition) -/
def diskMat01 (B : Matrix (Fin m) (Fin m) R) : FourCx R (Fin m) (Fin m) Empty Empty where
  d0 := B
  d1 := 0
  d2 := 0
  d10 := by simp
  d21 := by simp

/-- The matrix disk with cokernel in degree two: `C¹ = R^m --B--> R^m = C²`. (definition) -/
def diskMat12 (B : Matrix (Fin m) (Fin m) R) : FourCx R Empty (Fin m) (Fin m) Empty where
  d0 := 0
  d1 := B
  d2 := 0
  d10 := by simp
  d21 := by simp

/-- The matrix disk with cokernel in degree three: `C² = R^m --B--> R^m = C³`. (definition) -/
def diskMat23 (B : Matrix (Fin m) (Fin m) R) : FourCx R Empty Empty (Fin m) (Fin m) where
  d0 := 0
  d1 := 0
  d2 := B
  d10 := by simp
  d21 := by simp

/-- The contraction `B⁻¹` of `diskMat01 B` for `det B` a unit. (definition) -/
noncomputable def diskMat01Contraction (B : Matrix (Fin m) (Fin m) R) (hB : IsUnit B.det) :
    Contraction (diskMat01 B).toBased where
  hOE := 0
  hEO := fromBlocks B⁻¹ 0 0 0
  deg_hOE _ _ h := absurd rfl h
  deg_hEO := by
    rintro (u | e) (u' | e') h
    all_goals first | exact e.elim | exact e'.elim | rfl
  htpy_E := by
    ext (i | e) (j | e')
    all_goals try first | exact e.elim | exact e'.elim
    have := congrFun (congrFun (nonsing_inv_mul B hB) i) j
    simpa [FourCx.toBased, diskMat01, mul_apply, Fintype.sum_sum_type, one_apply] using this
  htpy_O := by
    ext (i | e) (j | e')
    all_goals try first | exact e.elim | exact e'.elim
    have := congrFun (congrFun (mul_nonsing_inv B hB) i) j
    simpa [FourCx.toBased, diskMat01, mul_apply, Fintype.sum_sum_type, one_apply] using this

/-- The contraction `B⁻¹` of `diskMat12 B` for `det B` a unit. (definition) -/
noncomputable def diskMat12Contraction (B : Matrix (Fin m) (Fin m) R) (hB : IsUnit B.det) :
    Contraction (diskMat12 B).toBased where
  hOE := fromBlocks 0 B⁻¹ 0 0
  hEO := 0
  deg_hOE := by
    rintro (u | e) (e' | u') h
    all_goals first | exact e.elim | exact e'.elim | rfl
  deg_hEO _ _ h := absurd rfl h
  htpy_E := by
    ext (e | i) (e' | j)
    all_goals try first | exact e.elim | exact e'.elim
    have := congrFun (congrFun (mul_nonsing_inv B hB) i) j
    simpa [FourCx.toBased, diskMat12, mul_apply, Fintype.sum_sum_type, one_apply] using this
  htpy_O := by
    ext (i | e) (j | e')
    all_goals try first | exact e.elim | exact e'.elim
    have := congrFun (congrFun (nonsing_inv_mul B hB) i) j
    simpa [FourCx.toBased, diskMat12, mul_apply, Fintype.sum_sum_type, one_apply] using this

/-- The contraction `B⁻¹` of `diskMat23 B` for `det B` a unit. (definition) -/
noncomputable def diskMat23Contraction (B : Matrix (Fin m) (Fin m) R) (hB : IsUnit B.det) :
    Contraction (diskMat23 B).toBased where
  hOE := 0
  hEO := fromBlocks 0 0 0 B⁻¹
  deg_hOE _ _ h := absurd rfl h
  deg_hEO := by
    rintro (e | u) (e' | u') h
    all_goals first | exact e.elim | exact e'.elim | rfl
  htpy_E := by
    ext (e | i) (e' | j)
    all_goals try first | exact e.elim | exact e'.elim
    have := congrFun (congrFun (nonsing_inv_mul B hB) i) j
    simpa [FourCx.toBased, diskMat23, mul_apply, Fintype.sum_sum_type, one_apply] using this
  htpy_O := by
    ext (e | i) (e' | j)
    all_goals try first | exact e.elim | exact e'.elim
    have := congrFun (congrFun (mul_nonsing_inv B hB) i) j
    simpa [FourCx.toBased, diskMat23, mul_apply, Fintype.sum_sum_type, one_apply] using this

/-- **The matrix disk with cokernel in degree one has torsion `det B`.** PROVED. -/
theorem torsion_diskMat01 [IsDomain R] (B : Matrix (Fin m) (Fin m) R) (hB : IsUnit B.det) :
    torsion (diskMat01 B).toBased (Equiv.refl _) = B.det := by
  rw [← tau_eq_torsion _ (diskMat01Contraction B hB)]
  unfold tau
  have : ((diskMat01 B).toBased.dOE + (diskMat01Contraction B hB).hOE).submatrix
      (Equiv.refl _) id = fromBlocks B 0 0 0 := by
    ext (i | e) (j | e')
    all_goals try first | exact e.elim | exact e'.elim
    simp [FourCx.toBased, diskMat01, diskMat01Contraction]
  rw [this, det_fromBlocks_zero₂₁]
  simp

/-- **The matrix disk with cokernel in degree two has torsion `(det B)⁻¹`.** PROVED. -/
theorem torsion_diskMat12 [IsDomain R] (B : Matrix (Fin m) (Fin m) R) (hB : IsUnit B.det) :
    torsion (diskMat12 B).toBased (Equiv.sumComm _ _) = ((hB.unit⁻¹ : Rˣ) : R) := by
  rw [← tau_eq_torsion _ (diskMat12Contraction B hB)]
  unfold tau
  have : ((diskMat12 B).toBased.dOE + (diskMat12Contraction B hB).hOE).submatrix
      (Equiv.sumComm _ _) id = fromBlocks 0 0 0 B⁻¹ := by
    ext (e | i) (e' | j)
    all_goals try first | exact e.elim | exact e'.elim
    simp [FourCx.toBased, diskMat12, diskMat12Contraction]
  rw [this, det_fromBlocks_zero₂₁, det_nonsing_inv]
  have e := Ring.inverse_unit hB.unit
  rw [hB.unit_spec] at e
  simp [e]

/-- **The matrix disk with cokernel in degree three has torsion `det B`.** PROVED. -/
theorem torsion_diskMat23 [IsDomain R] (B : Matrix (Fin m) (Fin m) R) (hB : IsUnit B.det) :
    torsion (diskMat23 B).toBased (Equiv.refl _) = B.det := by
  rw [← tau_eq_torsion _ (diskMat23Contraction B hB)]
  unfold tau
  have : ((diskMat23 B).toBased.dOE + (diskMat23Contraction B hB).hOE).submatrix
      (Equiv.refl _) id = fromBlocks 0 0 0 B := by
    ext (e | i) (e' | j)
    all_goals try first | exact e.elim | exact e'.elim
    simp [FourCx.toBased, diskMat23, diskMat23Contraction]
  rw [this, det_fromBlocks_zero₂₁]
  simp

end Disks

/-! ### The Kummer model with matrix disks -/

section KummerModelMat

variable {n m₁ m₂ m₃ : ℕ}

/-- The core `[R^n --D--> R^n]` plus matrix disks `B₁, B₂, B₃` with cokernels in degrees one,
two, three. (definition) -/
def kummerModelMat (D : Matrix (Fin n) (Fin n) R) (B₁ : Matrix (Fin m₁) (Fin m₁) R)
    (B₂ : Matrix (Fin m₂) (Fin m₂) R) (B₃ : Matrix (Fin m₃) (Fin m₃) R) :=
  (((twoTerm D).sum (diskMat01 B₁)).sum (diskMat12 B₂)).sum (diskMat23 B₃)

/-- The class extended by zero. (definition) -/
def kzM (z : Fin n → R) : ((Fin n ⊕ Fin m₁) ⊕ Fin m₂) ⊕ Empty → R :=
  Sum.elim (Sum.elim (Sum.elim z 0) 0) 0

/-- The functional extended by zero. (definition) -/
def kwM (w : Fin n → R) : ((Fin n ⊕ Empty) ⊕ Fin m₂) ⊕ Fin m₃ → R :=
  Sum.elim (Sum.elim (Sum.elim w 0) 0) 0

/-- The extended class is a cycle. PROVED. -/
theorem kummerModelMat_hz (D : Matrix (Fin n) (Fin n) R) (B₁ : Matrix (Fin m₁) (Fin m₁) R)
    (B₂ : Matrix (Fin m₂) (Fin m₂) R) (B₃ : Matrix (Fin m₃) (Fin m₃) R) {z : Fin n → R}
    (hz : (twoTerm D).d1 *ᵥ z = 0) : (kummerModelMat D B₁ B₂ B₃).d1 *ᵥ kzM z = 0 :=
  FourCx.sum_hz _ _ (FourCx.sum_hz _ _ (FourCx.sum_hz _ _ hz))

/-- The extended functional is closed. PROVED. -/
theorem kummerModelMat_hw (D : Matrix (Fin n) (Fin n) R) (B₁ : Matrix (Fin m₁) (Fin m₁) R)
    (B₂ : Matrix (Fin m₂) (Fin m₂) R) (B₃ : Matrix (Fin m₃) (Fin m₃) R) {w : Fin n → R}
    (hw : w ᵥ* (twoTerm D).d1 = 0) : kwM w ᵥ* (kummerModelMat D B₁ B₂ B₃).d1 = 0 :=
  FourCx.sum_hlam _ _ (FourCx.sum_hlam _ _ (FourCx.sum_hlam _ _ hw))

/-- The orientation of the Kummer model with matrix disks (as `σK`). (definition) -/
def σKM (n m₁ m₂ m₃ : ℕ) :=
  sumOrient (sumOrient (sumOrient (σ₀ n) (Equiv.refl (Fin m₁ ⊕ Empty)))
    (Equiv.sumComm Empty (Fin m₂))) (Equiv.refl (Empty ⊕ Fin m₃))

/-- **The coordinate of the Kummer model with matrix disks**: over a domain, if the augmented
core is acyclic and `z ⊗ λ = u · adj D`, then `kmCoord = u · det B₁ · (det B₂)⁻¹ · det B₃`.
PROVED. -/
theorem kmCoord_kummerModelMat [IsDomain R] (D : Matrix (Fin n) (Fin n) R) (z w : Fin n → R)
    (u : R) (hz : (twoTerm D).d1 *ᵥ z = 0) (hw : w ᵥ* (twoTerm D).d1 = 0)
    (h : Contraction ((twoTerm D).aug z w hz hw).toBased)
    (hu : ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord D z w u)
    (B₁ : Matrix (Fin m₁) (Fin m₁) R) (B₂ : Matrix (Fin m₂) (Fin m₂) R)
    (B₃ : Matrix (Fin m₃) (Fin m₃) R) (hB₁ : IsUnit B₁.det) (hB₂ : IsUnit B₂.det)
    (hB₃ : IsUnit B₃.det) :
    kmCoord (kummerModelMat D B₁ B₂ B₃) (kzM z) (kwM w) (kummerModelMat_hz D B₁ B₂ B₃ hz)
        (kummerModelMat_hw D B₁ B₂ B₃ hw) (σKM n m₁ m₂ m₃) =
      u * B₁.det * ((hB₂.unit⁻¹ : Rˣ) : R) * B₃.det := by
  have h1 := augSumContraction (twoTerm D) (diskMat01 B₁) z w hz hw h
    (diskMat01Contraction B₁ hB₁)
  have h2 := augSumContraction _ (diskMat12 B₂) _ _ _ _ h1 (diskMat12Contraction B₂ hB₂)
  unfold kummerModelMat kzM kwM σKM
  rw [kmCoord_sum _ _ _ _ _ _ h2 (diskMat23Contraction B₃ hB₃),
    kmCoord_sum _ _ _ _ _ _ h1 (diskMat12Contraction B₂ hB₂),
    kmCoord_sum _ _ _ _ _ _ h (diskMat01Contraction B₁ hB₁), kmCoord_twoTerm D z w u hz hw h hu,
    torsion_diskMat01 B₁ hB₁, torsion_diskMat12 B₂ hB₂, torsion_diskMat23 B₃ hB₃]

/-- **Matrix disks versus determinant disks**: the coordinate of the core plus matrix disks equals
the coordinate of the scalar Kummer model with disks `det B₁`, `det B₂`, `det B₃`. PROVED. -/
theorem kmCoord_kummerModelMat_eq_scalar [IsDomain R] (D : Matrix (Fin n) (Fin n) R)
    (z w : Fin n → R) (u : R) (hz : (twoTerm D).d1 *ᵥ z = 0) (hw : w ᵥ* (twoTerm D).d1 = 0)
    (h : Contraction ((twoTerm D).aug z w hz hw).toBased)
    (hu : ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord D z w u)
    (B₁ : Matrix (Fin m₁) (Fin m₁) R) (B₂ : Matrix (Fin m₂) (Fin m₂) R)
    (B₃ : Matrix (Fin m₃) (Fin m₃) R) (hB₁ : IsUnit B₁.det) (hB₂ : IsUnit B₂.det)
    (hB₃ : IsUnit B₃.det) :
    kmCoord (kummerModelMat D B₁ B₂ B₃) (kzM z) (kwM w) (kummerModelMat_hz D B₁ B₂ B₃ hz)
        (kummerModelMat_hw D B₁ B₂ B₃ hw) (σKM n m₁ m₂ m₃) =
      kmCoord (kummerModel D (hB₁.unit : R) hB₂.unit hB₃.unit) (kz z) (kw w)
        (kummerModel_hz D _ _ _ hz) (kummerModel_hw D _ _ _ hw) (σK n) := by
  rw [kmCoord_kummerModelMat D z w u hz hw h hu B₁ B₂ B₃ hB₁ hB₂ hB₃,
    kmCoord_kummerModel D z w u hz hw h hu hB₁.unit hB₂.unit hB₃.unit, hB₁.unit_spec,
    hB₃.unit_spec]

end KummerModelMat

/-! ### Invariance under boundaries -/

section Boundary

variable {ι0 ι1 ι2 ι3 : Type*} [Fintype ι0] [Fintype ι1] [Fintype ι2] [Fintype ι3]
  [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3]

omit [Fintype ι3] [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3] in
/-- A class plus a boundary is a cycle. PROVED. -/
theorem hz_add_boundary (C : FourCx R ι0 ι1 ι2 ι3) {z : ι1 → R} (hz : C.d1 *ᵥ z = 0)
    (x : ι0 → R) : C.d1 *ᵥ (z + C.d0 *ᵥ x) = 0 := by
  rw [mulVec_add, mulVec_mulVec, C.d10, zero_mulVec, hz, add_zero]

omit [Fintype ι0] [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3] in
/-- A functional plus a coboundary is closed. PROVED. -/
theorem hlam_add_coboundary (C : FourCx R ι0 ι1 ι2 ι3) {lam : ι2 → R}
    (hlam : lam ᵥ* C.d1 = 0) (μ : ι3 → R) : (lam + μ ᵥ* C.d2) ᵥ* C.d1 = 0 := by
  rw [add_vecMul, vecMul_vecMul, C.d21, vecMul_zero, hlam, add_zero]

omit [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3] in
/-- The augmented complex depends on the class only through its value. PROVED. -/
theorem aug_toBased_congr (C : FourCx R ι0 ι1 ι2 ι3) {z z' : ι1 → R} {lam : ι2 → R}
    (hz : C.d1 *ᵥ z = 0) (hz' : C.d1 *ᵥ z' = 0) (hlam : lam ᵥ* C.d1 = 0) (e : z = z') :
    (C.aug z lam hz hlam).toBased = (C.aug z' lam hz' hlam).toBased := by
  subst e; rfl

omit [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3] in
/-- The augmented complex depends on the functional only through its value. PROVED. -/
theorem aug_toBased_congr_lam (C : FourCx R ι0 ι1 ι2 ι3) {z : ι1 → R} {lam lam' : ι2 → R}
    (hz : C.d1 *ᵥ z = 0) (hlam : lam ᵥ* C.d1 = 0) (hlam' : lam' ᵥ* C.d1 = 0) (e : lam = lam') :
    (C.aug z lam hz hlam).toBased = (C.aug z lam' hz hlam').toBased := by
  subst e; rfl

/-- The unipotent column operation `[[1, x], [0, 1]]` on `C⁰ ⊕ R`. (definition) -/
def colOp (x : ι0 → R) : Matrix (ι0 ⊕ Unit) (ι0 ⊕ Unit) R := fromBlocks 1 (replicateCol Unit x) 0 1

/-- The unipotent row operation `[[1, 0], [μ, 1]]` on `C³ ⊕ R`. (definition) -/
def rowOp (μ : ι3 → R) : Matrix (ι3 ⊕ Unit) (ι3 ⊕ Unit) R := fromBlocks 1 0 (replicateRow Unit μ) 1

omit [Fintype ι1] [Fintype ι2] [Fintype ι3] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3] in
/-- Composition of column operations. PROVED. -/
theorem colOp_mul (x y : ι0 → R) : colOp x * colOp y = colOp (x + y) := by
  simp [colOp, fromBlocks_multiply, replicateCol_add, add_comm]

omit [Fintype ι0] [Fintype ι1] [Fintype ι2] [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] in
/-- Composition of row operations. PROVED. -/
theorem rowOp_mul (μ ν : ι3 → R) : rowOp μ * rowOp ν = rowOp (μ + ν) := by
  simp [rowOp, fromBlocks_multiply, replicateRow_add]

omit [Fintype ι1] [Fintype ι2] [Fintype ι3] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3] in
/-- A column operation has determinant one. PROVED. -/
theorem det_colOp (x : ι0 → R) : (colOp x).det = 1 := by
  simp [colOp]

omit [Fintype ι0] [Fintype ι1] [Fintype ι2] [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] in
/-- A row operation has determinant one. PROVED. -/
theorem det_rowOp (μ : ι3 → R) : (rowOp μ).det = 1 := by
  simp [rowOp]

/-- The graded change of basis `C⁰ ⊕ R`, `x`-column operation, of the augmented complex.
(definition) -/
def classChange (C : FourCx R ι0 ι1 ι2 ι3) (z : ι1 → R) (lam : ι2 → R) (hz : C.d1 *ᵥ z = 0)
    (hlam : lam ᵥ* C.d1 = 0) (x : ι0 → R) : GradedBasisChange (C.aug z lam hz hlam).toBased where
  Pe := fromBlocks (colOp (-x)) 0 0 1
  Qe := fromBlocks (colOp x) 0 0 1
  Po := 1
  Qo := 1
  hPQe := by
    rw [fromBlocks_multiply, colOp_mul, neg_add_cancel]
    simp [colOp, fromBlocks_one]
  hPQo := Matrix.one_mul 1
  deg_Pe := hasDeg_fromBlocks (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  deg_Qe := hasDeg_fromBlocks (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  deg_Po := hasDeg_one _
  deg_Qo := hasDeg_one _

/-- The graded change of basis `C³ ⊕ R`, `μ`-row operation, of the augmented complex.
(definition) -/
def funcChange (C : FourCx R ι0 ι1 ι2 ι3) (z : ι1 → R) (lam : ι2 → R) (hz : C.d1 *ᵥ z = 0)
    (hlam : lam ᵥ* C.d1 = 0) (μ : ι3 → R) : GradedBasisChange (C.aug z lam hz hlam).toBased where
  Pe := 1
  Qe := 1
  Po := fromBlocks 1 0 0 (rowOp μ)
  Qo := fromBlocks 1 0 0 (rowOp (-μ))
  hPQe := Matrix.one_mul 1
  hPQo := by
    rw [fromBlocks_multiply, rowOp_mul, add_neg_cancel]
    simp [rowOp, fromBlocks_one]
  deg_Pe := hasDeg_one _
  deg_Qe := hasDeg_one _
  deg_Po := hasDeg_fromBlocks (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  deg_Qo := hasDeg_fromBlocks (fun _ _ _ => rfl) (fun _ _ _ => rfl)

/-- Changing the class by a boundary `d⁰ x` is the column operation on the augmented complex.
PROVED. -/
theorem aug_add_boundary (C : FourCx R ι0 ι1 ι2 ι3) (z : ι1 → R) (lam : ι2 → R)
    (hz : C.d1 *ᵥ z = 0) (hlam : lam ᵥ* C.d1 = 0) (x : ι0 → R) :
    (C.aug (z + C.d0 *ᵥ x) lam (hz_add_boundary C hz x) hlam).toBased =
      (C.aug z lam hz hlam).toBased.rebase (classChange C z lam hz hlam x) := by
  apply BasedCx.ext'
  · rfl
  · rfl
  · ext x' y
    rcases x' with (a | (c | u)) <;> rcases y with ((a' | u') | b) <;>
      simp [FourCx.toBased, FourCx.aug, BasedCx.rebase, classChange, colOp, mul_apply,
        Fintype.sum_sum_type, mulVec, dotProduct, one_apply, add_comm]
  · ext x' y
    rcases x' with ((a' | u') | b) <;> rcases y with (a | (c | u)) <;>
      simp [FourCx.toBased, FourCx.aug, BasedCx.rebase, classChange, colOp, mul_apply,
        Fintype.sum_sum_type, one_apply]

/-- Changing the functional by a coboundary `μ d²` is the row operation on the augmented complex.
PROVED. -/
theorem aug_add_coboundary (C : FourCx R ι0 ι1 ι2 ι3) (z : ι1 → R) (lam : ι2 → R)
    (hz : C.d1 *ᵥ z = 0) (hlam : lam ᵥ* C.d1 = 0) (μ : ι3 → R) :
    (C.aug z (lam + μ ᵥ* C.d2) hz (hlam_add_coboundary C hlam μ)).toBased =
      (C.aug z lam hz hlam).toBased.rebase (funcChange C z lam hz hlam μ) := by
  apply BasedCx.ext'
  · rfl
  · rfl
  · ext x' y
    rcases x' with (a | (c | u)) <;> rcases y with ((a' | u') | b) <;>
      simp [FourCx.toBased, FourCx.aug, BasedCx.rebase, funcChange, rowOp, mul_apply,
        Fintype.sum_sum_type, vecMul, dotProduct, one_apply, add_comm]
  · ext x' y
    rcases x' with ((a' | u') | b) <;> rcases y with (a | (c | u)) <;>
      simp [FourCx.toBased, FourCx.aug, BasedCx.rebase, funcChange, rowOp, mul_apply,
        Fintype.sum_sum_type, one_apply]

/-- **The Knudsen–Mumford coordinate does not see boundaries in the class**: over a domain,
`kmCoord C (z + d⁰ x) λ = kmCoord C z λ` (whether or not the augmented complex is acyclic).
PROVED. -/
theorem kmCoord_add_boundary_class [IsDomain R] (C : FourCx R ι0 ι1 ι2 ι3) (z : ι1 → R)
    (lam : ι2 → R) (hz : C.d1 *ᵥ z = 0) (hlam : lam ᵥ* C.d1 = 0) (x : ι0 → R)
    (σ : (ι0 ⊕ Unit) ⊕ ι2 ≃ ι1 ⊕ (ι3 ⊕ Unit)) :
    kmCoord C (z + C.d0 *ᵥ x) lam (hz_add_boundary C hz x) hlam σ = kmCoord C z lam hz hlam σ := by
  unfold kmCoord
  congr 1
  by_cases hc : Nonempty (Contraction (C.aug z lam hz hlam).toBased)
  · obtain ⟨h⟩ := hc
    rw [aug_add_boundary C z lam hz hlam x, ← tau_eq_torsion _ (h.rebase _), tau_rebase,
      ← tau_eq_torsion _ h]
    simp [classChange, det_colOp]
  · have hc' : ¬ Nonempty (Contraction
        (C.aug (z + C.d0 *ᵥ x) lam (hz_add_boundary C hz x) hlam).toBased) := by
      rintro ⟨h'⟩
      apply hc
      have e : z + C.d0 *ᵥ x + C.d0 *ᵥ (-x) = z := by rw [mulVec_neg]; abel
      have h'' := h'.rebase (classChange C _ lam (hz_add_boundary C hz x) hlam (-x))
      rw [← aug_add_boundary, aug_toBased_congr C _ hz hlam e] at h''
      exact ⟨h''⟩
    simp [torsion, hc, hc']

/-- **The Knudsen–Mumford coordinate does not see coboundaries in the functional**: over a
domain, `kmCoord C z (λ + μ d²) = kmCoord C z λ`. PROVED. -/
theorem kmCoord_add_boundary_functional [IsDomain R] (C : FourCx R ι0 ι1 ι2 ι3) (z : ι1 → R)
    (lam : ι2 → R) (hz : C.d1 *ᵥ z = 0) (hlam : lam ᵥ* C.d1 = 0) (μ : ι3 → R)
    (σ : (ι0 ⊕ Unit) ⊕ ι2 ≃ ι1 ⊕ (ι3 ⊕ Unit)) :
    kmCoord C z (lam + μ ᵥ* C.d2) hz (hlam_add_coboundary C hlam μ) σ =
      kmCoord C z lam hz hlam σ := by
  unfold kmCoord
  congr 1
  by_cases hc : Nonempty (Contraction (C.aug z lam hz hlam).toBased)
  · obtain ⟨h⟩ := hc
    rw [aug_add_coboundary C z lam hz hlam μ, ← tau_eq_torsion _ (h.rebase _), tau_rebase,
      ← tau_eq_torsion _ h]
    simp [funcChange, det_fromBlocks_zero₂₁, det_rowOp]
  · have hc' : ¬ Nonempty (Contraction
        (C.aug z (lam + μ ᵥ* C.d2) hz (hlam_add_coboundary C hlam μ)).toBased) := by
      rintro ⟨h'⟩
      apply hc
      have e : lam + μ ᵥ* C.d2 + (-μ) ᵥ* C.d2 = lam := by rw [neg_vecMul]; abel
      have h'' := h'.rebase (funcChange C z _ hz (hlam_add_coboundary C hlam μ) (-μ))
      rw [← aug_add_coboundary, aug_toBased_congr_lam C hz _ hlam e] at h''
      exact ⟨h''⟩
    simp [torsion, hc, hc']

end Boundary

/-! ### Non-vacuity -/

/-- The disk `diag(2, 4)` over `ℚ` has unit determinant. PROVED. -/
theorem exB₁_isUnit : IsUnit (diagonal ![(2 : ℚ), 4]).det := by
  rw [det_diagonal, isUnit_iff_ne_zero]; simp [Fin.prod_univ_two]

/-- The disk `diag(8)` over `ℚ` has unit determinant. PROVED. -/
theorem exB₂_isUnit : IsUnit (diagonal ![(8 : ℚ)]).det := by
  rw [det_diagonal, isUnit_iff_ne_zero]; simp

/-- The identity disk has unit determinant. PROVED. -/
theorem exB₃_isUnit : IsUnit (1 : Matrix (Fin 1) (Fin 1) ℚ).det := by
  rw [det_one]; exact isUnit_one

/-- **Non-vacuity of `kmCoord_kummerModelMat`** over `ℚ`: core `D = (0)`, `z = λ = u = 1`,
matrix disks `diag(2, 4)`, `diag(8)`, `1`; the coordinate is `1 · 8 · 8⁻¹ · 1 = 1`. PROVED. -/
theorem kmCoord_kummerModelMat_example :
    kmCoord (kummerModelMat (0 : Matrix (Fin 1) (Fin 1) ℚ) (diagonal ![(2 : ℚ), 4])
        (diagonal ![(8 : ℚ)]) (1 : Matrix (Fin 1) (Fin 1) ℚ)) (kzM 1) (kwM 1)
        (kummerModelMat_hz _ _ _ _ twoTerm_zero_hz) (kummerModelMat_hw _ _ _ _ twoTerm_zero_hw)
        (σKM 1 2 1 1) = 1 := by
  rw [kmCoord_kummerModelMat _ 1 1 1 _ _ twoTermContraction_example ?_ _ _ _ exB₁_isUnit
    exB₂_isUnit exB₃_isUnit]
  · rw [Units.val_inv_eq_inv_val, IsUnit.unit_spec]
    simp [det_diagonal, Fin.prod_univ_two]
    norm_num
  · unfold ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord
    ext i j
    fin_cases i; fin_cases j
    simp [vecMulVec_apply, adjugate_fin_one]

end ZInQ.Manuscript.RC.Wiring.KmIdent

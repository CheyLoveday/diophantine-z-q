import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.FullConditionCoord
import ZInQKernel.Contrib.CloudB3RC53.Torsion.Cone
import ZInQKernel.Contrib.CloudB3RC53.Torsion.KummerDisks
import ZInQKernel.Contrib.CloudB3RC53.CommonCoordinate.Triangular
import ZInQKernel.Contrib.OneProof.RC.Central.Correction

/-!
# Lane RC31, round 4: the Knudsen–Mumford coordinate is bilinear in the cycle and the functional

Manuscript `diophantine_zq.tex`, the coordinate of Definition `ex:arith-coordinate` (tex
3877–3892: the coordinate of `[z] ⊗ [λ]` in `det⁻¹ C ≅ H¹ ⊗ (H²)^*`) and the support triangle of
Lemma `ex:arith-common-coordinate` (tex 4157–4194: `λ_R ∘ i = e_q λ_P`, `z_R = e_q i(z_P)`).

The tree's `kmCoord C z λ σ` is minus the torsion of the augmented complex
`C⁰ ⊕ K --(d⁰, z)--> C¹ --d¹--> C² --(d², λ)--> C³ ⊕ K`. Over a field `K` this file proves that it
is a bilinear function of the class of the cycle and the class of the functional:

* homogeneity: `kmCoord (c • z) λ = c · kmCoord z λ` and `kmCoord z (c • λ) = c · kmCoord z λ`
  for every `c : K` (`kmCoord_smul_z`, `kmCoord_smul_lam`): for `c ≠ 0` a graded change of basis
  of the augmentation lines (`torsion_rebase'`), for `c = 0` the augmented complex has no
  contraction;
* dependence on the classes only: `kmCoord (z + d⁰ w) λ = kmCoord z λ` and
  `kmCoord z (λ + μ d²) = kmCoord z λ` (`kmCoord_add_boundary`, `kmCoord_add_coboundary`):
  unipotent changes of basis; hence `kmCoord` vanishes on boundaries and on coboundaries;
* additivity in each argument (`kmCoord_add_z`, `kmCoord_add_lam`), with no rank hypothesis: if
  one class is a multiple of the other modulo boundaries this is the homogeneity, otherwise a
  second independent class obstructs every contraction (`not_contraction_of_independent_z`,
  `not_contraction_of_independent_lam`) and all three coordinates vanish;
* the bilinear form `kmCoordBilin` on cycles and closed functionals;
* the step relation of the support triangle: with `z ∘ inl = e • z_P` and `λ ∘ inl = e • λ_P`
  on the remaining complex of a `FullPreComplex`,
  `kmCoord(C, z, λ) = det(B)⁻¹ · e² · kmCoord(C.cancel, z_P, λ_P)` (`kmCoord_fullCancel_step`),
  and with `B` the two-place singular block, `l_q u_R = e_q² q⁻⁴ u_P` (`kmCoord_step_47`).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open Matrix ZInQ.Contrib.CloudB3RC53.Torsion ZInQ.Contrib.CloudB3RC53.ClearingComplex
open ZInQ.Contrib.CloudB3RC53.CommonCoordinate (twoPlaceBlock det_twoPlaceBlock)
open ZInQ.Manuscript.RC.Central (pointFactor quotientFactor quotientDet quotientDet_eq
  det_one_sub_smul)

section Generic

variable {K : Type} [Field K]

/-- A block-diagonal matrix has degree zero for a two-valued degree function.
(tex 3877–3892) Kind: PROVED. -/
theorem hasDeg_fromBlocks_diag {α β : Type} (A : Matrix α α K) (D : Matrix β β K) (a b : ℤ) :
    HasDeg (fromBlocks A 0 0 D) (Sum.elim (fun _ => a) (fun _ => b))
      (Sum.elim (fun _ => a) (fun _ => b)) 0 := by
  rintro (i | i) (j | j) h
  · simp
  · exact absurd rfl h
  · exact absurd rfl h
  · simp

end Generic

/-! ### Graded changes of basis of the augmentation lines -/

section LinesE

variable {K : Type} [Field K] {ι0 ι2 : Type} [Fintype ι0] [Fintype ι2] [DecidableEq ι0]
  [DecidableEq ι2]

/-- Scaling the degree-zero augmentation line by `c`. (tex 3877–3892) Kind: definition. -/
def eLine (c : K) : Matrix ((ι0 ⊕ Unit) ⊕ ι2) ((ι0 ⊕ Unit) ⊕ ι2) K :=
  fromBlocks (fromBlocks 1 0 0 (c • 1)) 0 0 1

/-- Adding `w` to the degree-zero augmentation line. (tex 3877–3892) Kind: definition. -/
def eShear (w : ι0 → K) : Matrix ((ι0 ⊕ Unit) ⊕ ι2) ((ι0 ⊕ Unit) ⊕ ι2) K :=
  fromBlocks (fromBlocks 1 (replicateCol Unit w) 0 1) 0 0 1

/-- The inverse of a line scaling. (tex 3877–3892) Kind: PROVED. -/
theorem eLine_mul {c d : K} (h : c * d = 1) :
    (eLine (ι0 := ι0) (ι2 := ι2) c) * eLine d = 1 := by
  simp only [eLine, fromBlocks_multiply, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add, smul_mul_smul_comm, h, one_smul, fromBlocks_one]

/-- The inverse of a shear. (tex 3877–3892) Kind: PROVED. -/
theorem eShear_mul (w : ι0 → K) : (eShear (ι2 := ι2) (-w)) * eShear w = 1 := by
  have h0 : replicateCol Unit w + replicateCol Unit (-w) = (0 : Matrix ι0 Unit K) := by
    ext; simp
  simp only [eShear, fromBlocks_multiply, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add, Matrix.one_mul, h0, fromBlocks_one]

end LinesE

section LinesO

variable {K : Type} [Field K] {ι1 ι3 : Type} [Fintype ι1] [Fintype ι3] [DecidableEq ι1]
  [DecidableEq ι3]

/-- Scaling the degree-three augmentation line by `c`. (tex 3877–3892) Kind: definition. -/
def oLine (c : K) : Matrix (ι1 ⊕ (ι3 ⊕ Unit)) (ι1 ⊕ (ι3 ⊕ Unit)) K :=
  fromBlocks 1 0 0 (fromBlocks 1 0 0 (c • 1))

/-- Adding `μ` to the degree-three augmentation line. (tex 3877–3892) Kind: definition. -/
def oShear (μ : ι3 → K) : Matrix (ι1 ⊕ (ι3 ⊕ Unit)) (ι1 ⊕ (ι3 ⊕ Unit)) K :=
  fromBlocks 1 0 0 (fromBlocks 1 0 (replicateRow Unit μ) 1)

/-- The inverse of a line scaling. (tex 3877–3892) Kind: PROVED. -/
theorem oLine_mul {c d : K} (h : c * d = 1) :
    (oLine (ι1 := ι1) (ι3 := ι3) c) * oLine d = 1 := by
  simp only [oLine, fromBlocks_multiply, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add, smul_mul_smul_comm, h, one_smul, fromBlocks_one]

/-- The inverse of a shear. (tex 3877–3892) Kind: PROVED. -/
theorem oShear_mul (μ : ι3 → K) : (oShear (ι1 := ι1) μ) * oShear (-μ) = 1 := by
  have h0 : replicateRow Unit μ + replicateRow Unit (-μ) = (0 : Matrix Unit ι3 K) := by
    ext; simp
  simp only [oShear, fromBlocks_multiply, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add, Matrix.one_mul, h0, fromBlocks_one]

end LinesO

variable {K : Type} [Field K] {ι0 ι1 ι2 ι3 : Type} [Fintype ι0] [Fintype ι1] [Fintype ι2]
  [Fintype ι3] [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3]
  (C : FourCx K ι0 ι1 ι2 ι3)

/-! ### Congruence and the cycle conditions -/

/-- `kmCoord` depends only on the cycle and the functional (not on the proofs).
(tex 3877–3892) Kind: PROVED. -/
theorem kmCoord_congr {z z' : ι1 → K} {lam lam' : ι2 → K} (hz : C.d1 *ᵥ z = 0)
    (hz' : C.d1 *ᵥ z' = 0) (hlam : lam ᵥ* C.d1 = 0) (hlam' : lam' ᵥ* C.d1 = 0) (h1 : z = z')
    (h2 : lam = lam') (σ : (ι0 ⊕ Unit) ⊕ ι2 ≃ ι1 ⊕ (ι3 ⊕ Unit)) :
    kmCoord C z lam hz hlam σ = kmCoord C z' lam' hz' hlam' σ := by
  subst h1 h2
  rfl

omit [Fintype ι0] [Fintype ι3] [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2]
  [DecidableEq ι3] in
/-- A multiple of a cycle is a cycle. (tex 3877–3892) Kind: PROVED. -/
theorem cycle_smul {z : ι1 → K} (hz : C.d1 *ᵥ z = 0) (c : K) : C.d1 *ᵥ (c • z) = 0 := by
  rw [mulVec_smul, hz, smul_zero]

omit [Fintype ι0] [Fintype ι3] [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2]
  [DecidableEq ι3] in
/-- A multiple of a closed functional is closed. (tex 3877–3892) Kind: PROVED. -/
theorem closed_smul {lam : ι2 → K} (hlam : lam ᵥ* C.d1 = 0) (c : K) :
    (c • lam) ᵥ* C.d1 = 0 := by
  rw [smul_vecMul, hlam, smul_zero]

omit [Fintype ι3] [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3] in
/-- A cycle plus a boundary is a cycle. (tex 3877–3892) Kind: PROVED. -/
theorem cycle_add_boundary {z : ι1 → K} (hz : C.d1 *ᵥ z = 0) (w : ι0 → K) :
    C.d1 *ᵥ (z + C.d0 *ᵥ w) = 0 := by
  rw [mulVec_add, hz, zero_add, mulVec_mulVec, C.d10, zero_mulVec]

omit [Fintype ι0] [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3] in
/-- A closed functional plus a coboundary is closed. (tex 3877–3892) Kind: PROVED. -/
theorem closed_add_coboundary {lam : ι2 → K} (hlam : lam ᵥ* C.d1 = 0) (μ : ι3 → K) :
    (lam + μ ᵥ* C.d2) ᵥ* C.d1 = 0 := by
  rw [add_vecMul, hlam, zero_add, vecMul_vecMul, C.d21, vecMul_zero]

/-! ### The zero cases: no contraction -/

/-- **With the zero cycle the augmented complex is not contractible**: the augmentation line in
degree zero is a cycle. (tex 3877–3892) Kind: PROVED. -/
theorem not_contraction_aug_zero_z {lam : ι2 → K} (h0 : C.d1 *ᵥ (0 : ι1 → K) = 0)
    (hlam : lam ᵥ* C.d1 = 0) : ¬ Nonempty (Contraction (C.aug 0 lam h0 hlam).toBased) := by
  rintro ⟨h⟩
  have e := congrFun (congrFun h.htpy_E (Sum.inl (Sum.inr ()))) (Sum.inl (Sum.inr ()))
  simp [Matrix.add_apply, Matrix.mul_apply, FourCx.toBased, FourCx.aug, Fintype.sum_sum_type]
    at e

/-- **With the zero functional the augmented complex is not contractible**: the augmentation line
in degree three is not a boundary. (tex 3877–3892) Kind: PROVED. -/
theorem not_contraction_aug_zero_lam {z : ι1 → K} (hz : C.d1 *ᵥ z = 0)
    (h0 : (0 : ι2 → K) ᵥ* C.d1 = 0) : ¬ Nonempty (Contraction (C.aug z 0 hz h0).toBased) := by
  rintro ⟨h⟩
  have e := congrFun (congrFun h.htpy_O (Sum.inr (Sum.inr ()))) (Sum.inr (Sum.inr ()))
  simp [Matrix.add_apply, Matrix.mul_apply, FourCx.toBased, FourCx.aug, Fintype.sum_sum_type]
    at e

/-- `kmCoord` vanishes at the zero cycle. (tex 3877–3892) Kind: PROVED. -/
theorem kmCoord_zero_z {lam : ι2 → K} (h0 : C.d1 *ᵥ (0 : ι1 → K) = 0) (hlam : lam ᵥ* C.d1 = 0)
    (σ : (ι0 ⊕ Unit) ⊕ ι2 ≃ ι1 ⊕ (ι3 ⊕ Unit)) : kmCoord C 0 lam h0 hlam σ = 0 := by
  unfold kmCoord torsion
  simp [not_contraction_aug_zero_z C h0 hlam]

/-- `kmCoord` vanishes at the zero functional. (tex 3877–3892) Kind: PROVED. -/
theorem kmCoord_zero_lam {z : ι1 → K} (hz : C.d1 *ᵥ z = 0) (h0 : (0 : ι2 → K) ᵥ* C.d1 = 0)
    (σ : (ι0 ⊕ Unit) ⊕ ι2 ≃ ι1 ⊕ (ι3 ⊕ Unit)) : kmCoord C z 0 hz h0 σ = 0 := by
  unfold kmCoord torsion
  simp [not_contraction_aug_zero_lam C hz h0]

/-! ### The four changes of basis of the augmented complex -/

section Changes

variable {z : ι1 → K} {lam : ι2 → K} (hz : C.d1 *ᵥ z = 0) (hlam : lam ᵥ* C.d1 = 0)

/-- The change of basis scaling the degree-zero augmentation line by `c ≠ 0`. (tex 3877–3892) Kind:
definition. -/
def zScaleChange {c : K} (hc : c ≠ 0) : GradedBasisChange (C.aug z lam hz hlam).toBased where
  Pe := eLine c⁻¹
  Qe := eLine c
  Po := 1
  Qo := 1
  hPQe := eLine_mul (inv_mul_cancel₀ hc)
  hPQo := Matrix.one_mul 1
  deg_Pe := hasDeg_fromBlocks_diag _ _ 0 2
  deg_Qe := hasDeg_fromBlocks_diag _ _ 0 2
  deg_Po := hasDeg_one _
  deg_Qo := hasDeg_one _

/-- The change of basis scaling the degree-three augmentation line by `c ≠ 0`. (tex 3877–3892) Kind:
definition. -/
def lamScaleChange {c : K} (hc : c ≠ 0) : GradedBasisChange (C.aug z lam hz hlam).toBased where
  Pe := 1
  Qe := 1
  Po := oLine c
  Qo := oLine c⁻¹
  hPQe := Matrix.one_mul 1
  hPQo := oLine_mul (mul_inv_cancel₀ hc)
  deg_Pe := hasDeg_one _
  deg_Qe := hasDeg_one _
  deg_Po := hasDeg_fromBlocks_diag _ _ 1 3
  deg_Qo := hasDeg_fromBlocks_diag _ _ 1 3

/-- The change of basis adding a boundary `d⁰ w` to the cycle. (tex 3877–3892) Kind: definition. -/
def zShearChange (w : ι0 → K) : GradedBasisChange (C.aug z lam hz hlam).toBased where
  Pe := eShear (-w)
  Qe := eShear w
  Po := 1
  Qo := 1
  hPQe := eShear_mul w
  hPQo := Matrix.one_mul 1
  deg_Pe := hasDeg_fromBlocks_diag _ _ 0 2
  deg_Qe := hasDeg_fromBlocks_diag _ _ 0 2
  deg_Po := hasDeg_one _
  deg_Qo := hasDeg_one _

/-- The change of basis adding a coboundary `μ d²` to the functional.
(tex 3877–3892) Kind: definition. -/
def lamShearChange (μ : ι3 → K) : GradedBasisChange (C.aug z lam hz hlam).toBased where
  Pe := 1
  Qe := 1
  Po := oShear μ
  Qo := oShear (-μ)
  hPQe := Matrix.one_mul 1
  hPQo := oShear_mul μ
  deg_Pe := hasDeg_one _
  deg_Qe := hasDeg_one _
  deg_Po := hasDeg_fromBlocks_diag _ _ 1 3
  deg_Qo := hasDeg_fromBlocks_diag _ _ 1 3

/-- Scaling the cycle is the line scaling. (tex 3877–3892) Kind: PROVED. -/
theorem aug_smul_z {c : K} (hc : c ≠ 0) :
    (C.aug (c • z) lam (cycle_smul C hz c) hlam).toBased =
      (C.aug z lam hz hlam).toBased.rebase (zScaleChange C hz hlam hc) := by
  refine BasedCx.ext' rfl rfl ?_ ?_
  · ext i j
    rcases i with i | (i | i) <;> rcases j with (j | j) | j <;>
      simp [BasedCx.rebase, zScaleChange, FourCx.toBased, FourCx.aug, eLine, Matrix.mul_apply,
        Fintype.sum_sum_type, Matrix.one_apply, mul_comm]
  · ext i j
    rcases i with (i | i) | i <;> rcases j with j | (j | j) <;>
      simp [BasedCx.rebase, zScaleChange, FourCx.toBased, FourCx.aug, eLine, Matrix.mul_apply,
        Fintype.sum_sum_type, Matrix.one_apply]

/-- Scaling the functional is the line scaling. (tex 3877–3892) Kind: PROVED. -/
theorem aug_smul_lam {c : K} (hc : c ≠ 0) :
    (C.aug z (c • lam) hz (closed_smul C hlam c)).toBased =
      (C.aug z lam hz hlam).toBased.rebase (lamScaleChange C hz hlam hc) := by
  refine BasedCx.ext' rfl rfl ?_ ?_
  · ext i j
    rcases i with i | (i | i) <;> rcases j with (j | j) | j <;>
      simp [BasedCx.rebase, lamScaleChange, FourCx.toBased, FourCx.aug, oLine, Matrix.mul_apply,
        Fintype.sum_sum_type, Matrix.one_apply, mul_comm]
  · ext i j
    rcases i with (i | i) | i <;> rcases j with j | (j | j) <;>
      simp [BasedCx.rebase, lamScaleChange, FourCx.toBased, FourCx.aug, oLine, Matrix.mul_apply,
        Fintype.sum_sum_type, Matrix.one_apply]

/-- Adding a boundary to the cycle is the shear. (tex 3877–3892) Kind: PROVED. -/
theorem aug_add_boundary (w : ι0 → K) :
    (C.aug (z + C.d0 *ᵥ w) lam (cycle_add_boundary C hz w) hlam).toBased =
      (C.aug z lam hz hlam).toBased.rebase (zShearChange C hz hlam w) := by
  refine BasedCx.ext' rfl rfl ?_ ?_
  · ext i j
    rcases i with i | (i | i) <;> rcases j with (j | j) | j <;>
      simp [BasedCx.rebase, zShearChange, FourCx.toBased, FourCx.aug, eShear, Matrix.mul_apply,
        Fintype.sum_sum_type, Matrix.one_apply, mulVec, dotProduct, add_comm]
  · ext i j
    rcases i with (i | i) | i <;> rcases j with j | (j | j) <;>
      simp [BasedCx.rebase, zShearChange, FourCx.toBased, FourCx.aug, eShear, Matrix.mul_apply,
        Fintype.sum_sum_type, Matrix.one_apply]

/-- Adding a coboundary to the functional is the shear. (tex 3877–3892) Kind: PROVED. -/
theorem aug_add_coboundary (μ : ι3 → K) :
    (C.aug z (lam + μ ᵥ* C.d2) hz (closed_add_coboundary C hlam μ)).toBased =
      (C.aug z lam hz hlam).toBased.rebase (lamShearChange C hz hlam μ) := by
  refine BasedCx.ext' rfl rfl ?_ ?_
  · ext i j
    rcases i with i | (i | i) <;> rcases j with (j | j) | j <;>
      simp [BasedCx.rebase, lamShearChange, FourCx.toBased, FourCx.aug, oShear, Matrix.mul_apply,
        Fintype.sum_sum_type, Matrix.one_apply, vecMul, dotProduct, add_comm]
  · ext i j
    rcases i with (i | i) | i <;> rcases j with j | (j | j) <;>
      simp [BasedCx.rebase, lamShearChange, FourCx.toBased, FourCx.aug, oShear, Matrix.mul_apply,
        Fintype.sum_sum_type, Matrix.one_apply]

end Changes

/-! ### Determinants of the changes of basis -/

section Dets

variable {K : Type} [Field K] {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-- The determinant of a line scaling. (tex 3877–3892) Kind: PROVED. -/
theorem det_lineE (c : K) :
    (fromBlocks (fromBlocks (1 : Matrix α α K) 0 0 (c • (1 : Matrix Unit Unit K))) 0 0
      (1 : Matrix β β K)).det = c := by
  rw [det_fromBlocks_zero₂₁, det_fromBlocks_zero₂₁, det_one, det_one, det_smul, det_one,
    Fintype.card_unit, pow_one]
  ring

/-- The determinant of a line scaling on the odd side. (tex 3877–3892) Kind: PROVED. -/
theorem det_lineO (c : K) :
    (fromBlocks (1 : Matrix α α K) 0 0
      (fromBlocks (1 : Matrix β β K) 0 0 (c • (1 : Matrix Unit Unit K)))).det = c := by
  rw [det_fromBlocks_zero₂₁, det_fromBlocks_zero₂₁, det_one, det_one, det_smul, det_one,
    Fintype.card_unit, pow_one]
  ring

/-- The determinant of a shear on the even side. (tex 3877–3892) Kind: PROVED. -/
theorem det_shearE (w : α → K) :
    (fromBlocks (fromBlocks (1 : Matrix α α K) (replicateCol Unit w) 0 (1 : Matrix Unit Unit K))
      0 0 (1 : Matrix β β K)).det = 1 := by
  rw [det_fromBlocks_zero₂₁, det_fromBlocks_zero₂₁, det_one, det_one, det_one, mul_one, mul_one]

/-- The determinant of a shear on the odd side. (tex 3877–3892) Kind: PROVED. -/
theorem det_shearO (μ : β → K) :
    (fromBlocks (1 : Matrix α α K) 0 0
      (fromBlocks (1 : Matrix β β K) 0 (replicateRow Unit μ) (1 : Matrix Unit Unit K))).det =
      1 := by
  rw [det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂, det_one, det_one, det_one, mul_one, mul_one]

end Dets

/-! ### Homogeneity and dependence on the classes -/

section Coord

variable {K : Type} [Field K] {ι0 ι1 ι2 ι3 : Type} [Fintype ι0] [Fintype ι1] [Fintype ι2]
  [Fintype ι3] [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3]
  (C : FourCx K ι0 ι1 ι2 ι3) {z : ι1 → K} {lam : ι2 → K} (hz : C.d1 *ᵥ z = 0)
  (hlam : lam ᵥ* C.d1 = 0) (σ : (ι0 ⊕ Unit) ⊕ ι2 ≃ ι1 ⊕ (ι3 ⊕ Unit))

/-- **The coordinate is homogeneous in the cycle**: `kmCoord(c z, λ) = c · kmCoord(z, λ)` for every
`c` (tex 3877–3892: the coordinate of `[z] ⊗ [λ]`). Kind: PROVED. -/
theorem kmCoord_smul_z (c : K) :
    kmCoord C (c • z) lam (cycle_smul C hz c) hlam σ = c * kmCoord C z lam hz hlam σ := by
  by_cases hc : c = 0
  · subst hc
    rw [zero_mul]
    rw [kmCoord_congr C (cycle_smul C hz 0) (by simp) hlam hlam (zero_smul K z) rfl σ]
    exact kmCoord_zero_z C _ hlam σ
  · unfold kmCoord
    rw [aug_smul_z C hz hlam hc, torsion_rebase']
    change -((1 : Matrix (ι1 ⊕ (ι3 ⊕ Unit)) (ι1 ⊕ (ι3 ⊕ Unit)) K).det *
      torsion (C.aug z lam hz hlam).toBased σ * (eLine (ι0 := ι0) (ι2 := ι2) c).det) = _
    rw [det_one, eLine, det_lineE]
    ring

/-- **The coordinate is homogeneous in the functional**: `kmCoord(z, c λ) = c · kmCoord(z, λ)` for
every `c`. (tex 3877–3892) Kind: PROVED. -/
theorem kmCoord_smul_lam (c : K) :
    kmCoord C z (c • lam) hz (closed_smul C hlam c) σ = c * kmCoord C z lam hz hlam σ := by
  by_cases hc : c = 0
  · subst hc
    rw [zero_mul]
    rw [kmCoord_congr C hz hz (closed_smul C hlam 0) (by simp) rfl (zero_smul K lam) σ]
    exact kmCoord_zero_lam C hz _ σ
  · unfold kmCoord
    rw [aug_smul_lam C hz hlam hc, torsion_rebase']
    change -((oLine (ι1 := ι1) (ι3 := ι3) c).det *
      torsion (C.aug z lam hz hlam).toBased σ *
        (1 : Matrix ((ι0 ⊕ Unit) ⊕ ι2) ((ι0 ⊕ Unit) ⊕ ι2) K).det) = _
    rw [det_one, oLine, det_lineO]
    ring

/-- **The coordinate depends only on the class of the cycle**: `kmCoord(z + d⁰ w, λ) =
kmCoord(z, λ)`. (tex 3877–3892) Kind: PROVED. -/
theorem kmCoord_add_boundary (w : ι0 → K) :
    kmCoord C (z + C.d0 *ᵥ w) lam (cycle_add_boundary C hz w) hlam σ =
      kmCoord C z lam hz hlam σ := by
  unfold kmCoord
  rw [aug_add_boundary C hz hlam w, torsion_rebase']
  change -((1 : Matrix (ι1 ⊕ (ι3 ⊕ Unit)) (ι1 ⊕ (ι3 ⊕ Unit)) K).det *
    torsion (C.aug z lam hz hlam).toBased σ * (eShear (ι2 := ι2) w).det) = _
  rw [det_one, eShear, det_shearE]
  ring

/-- **The coordinate depends only on the class of the functional**: `kmCoord(z, λ + μ d²) =
kmCoord(z, λ)`. (tex 3877–3892) Kind: PROVED. -/
theorem kmCoord_add_coboundary (μ : ι3 → K) :
    kmCoord C z (lam + μ ᵥ* C.d2) hz (closed_add_coboundary C hlam μ) σ =
      kmCoord C z lam hz hlam σ := by
  unfold kmCoord
  rw [aug_add_coboundary C hz hlam μ, torsion_rebase']
  change -((oShear (ι1 := ι1) μ).det * torsion (C.aug z lam hz hlam).toBased σ *
    (1 : Matrix ((ι0 ⊕ Unit) ⊕ ι2) ((ι0 ⊕ Unit) ⊕ ι2) K).det) = _
  rw [det_one, oShear, det_shearO]
  ring

/-- **The coordinate vanishes on boundaries.** (tex 3877–3892) Kind: PROVED. -/
theorem kmCoord_boundary (w : ι0 → K) (hb : C.d1 *ᵥ (C.d0 *ᵥ w) = 0) :
    kmCoord C (C.d0 *ᵥ w) lam hb hlam σ = 0 := by
  have h0 : C.d1 *ᵥ (0 : ι1 → K) = 0 := by simp
  rw [kmCoord_congr C hb (cycle_add_boundary C h0 w) hlam hlam (zero_add _).symm rfl σ,
    kmCoord_add_boundary C h0 hlam σ w]
  exact kmCoord_zero_z C h0 hlam σ

/-- **The coordinate vanishes on coboundaries.** (tex 3877–3892) Kind: PROVED. -/
theorem kmCoord_coboundary (μ : ι3 → K) (hb : (μ ᵥ* C.d2) ᵥ* C.d1 = 0) :
    kmCoord C z (μ ᵥ* C.d2) hz hb σ = 0 := by
  have h0 : (0 : ι2 → K) ᵥ* C.d1 = 0 := by simp
  rw [kmCoord_congr C hz hz hb (closed_add_coboundary C h0 μ) rfl (zero_add _).symm σ,
    kmCoord_add_coboundary C hz h0 σ μ]
  exact kmCoord_zero_lam C hz h0 σ

/-- **Bihomogeneity**: `kmCoord(a z, b λ) = a b · kmCoord(z, λ)`. (tex 3877–3892) Kind: PROVED. -/
theorem kmCoord_smul_smul (a b : K) :
    kmCoord C (a • z) (b • lam) (cycle_smul C hz a) (closed_smul C hlam b) σ =
      a * b * kmCoord C z lam hz hlam σ := by
  rw [kmCoord_smul_lam C (cycle_smul C hz a) hlam σ b, kmCoord_smul_z C hz hlam σ a]
  ring

end Coord

/-! ### Additivity -/

section Additive

variable {K : Type} [Field K] {ι0 ι1 ι2 ι3 : Type} [Fintype ι0] [Fintype ι1] [Fintype ι2]
  [Fintype ι3] [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3]
  (C : FourCx K ι0 ι1 ι2 ι3) (σ : (ι0 ⊕ Unit) ⊕ ι2 ≃ ι1 ⊕ (ι3 ⊕ Unit))

/-- `kmCoord` vanishes when the augmented complex has no contraction.
(tex 3877–3892) Kind: PROVED. -/
theorem kmCoord_eq_zero_of_not {z : ι1 → K} {lam : ι2 → K} (hz : C.d1 *ᵥ z = 0)
    (hlam : lam ᵥ* C.d1 = 0) (h : ¬ Nonempty (Contraction (C.aug z lam hz hlam).toBased)) :
    kmCoord C z lam hz hlam σ = 0 := by
  unfold kmCoord torsion
  simp [h]

/-- **A second independent class obstructs the contraction**: if a cycle `z'` is not in
`K z + im d⁰`, the augmented complex of `z` is not contractible (its degree-one cohomology is not
spanned by `[z]`). (tex 3877–3892) Kind: PROVED. -/
theorem not_contraction_of_independent_z {z : ι1 → K} {lam : ι2 → K} (hz : C.d1 *ᵥ z = 0)
    (hlam : lam ᵥ* C.d1 = 0) {z' : ι1 → K} (hz' : C.d1 *ᵥ z' = 0)
    (hind : ∀ (t : K) (w : ι0 → K), z' ≠ t • z + C.d0 *ᵥ w) :
    ¬ Nonempty (Contraction (C.aug z lam hz hlam).toBased) := by
  rintro ⟨h⟩
  let v : ι1 ⊕ (ι3 ⊕ Unit) → K := Sum.elim z' 0
  have hdv : (C.aug z lam hz hlam).toBased.dEO *ᵥ v = 0 := by
    funext k
    rcases k with (k | k) | k
    · simp [FourCx.toBased, FourCx.aug, mulVec, dotProduct, Fintype.sum_sum_type, v]
    · simp [FourCx.toBased, FourCx.aug, mulVec, dotProduct, Fintype.sum_sum_type, v]
    · have e := congrFun hz' k
      simpa [FourCx.toBased, FourCx.aug, mulVec, dotProduct, Fintype.sum_sum_type, v] using e
  have e1 : v = (C.aug z lam hz hlam).toBased.dOE *ᵥ (h.hEO *ᵥ v) := by
    have e := congrArg (fun M => M *ᵥ v) h.htpy_O
    simp only [add_mulVec, one_mulVec, ← mulVec_mulVec, hdv, mulVec_zero, add_zero] at e
    exact e.symm
  set u := h.hEO *ᵥ v with hu
  clear_value u
  apply hind (u (Sum.inl (Sum.inr ()))) (fun a => u (Sum.inl (Sum.inl a)))
  funext i
  have e := congrFun e1 (Sum.inl i)
  have e' : v (Sum.inl i) = z' i := rfl
  rw [e'] at e
  rw [e]
  simp [FourCx.toBased, FourCx.aug, mulVec, dotProduct, Fintype.sum_sum_type]
  ring

/-- **A second independent class obstructs the contraction, dually**: if a closed functional `λ'`
is not in `K λ + im (d²)^*`, the augmented complex of `λ` is not contractible.
(tex 3877–3892) Kind: PROVED. -/
theorem not_contraction_of_independent_lam {z : ι1 → K} {lam : ι2 → K} (hz : C.d1 *ᵥ z = 0)
    (hlam : lam ᵥ* C.d1 = 0) {lam' : ι2 → K} (hlam' : lam' ᵥ* C.d1 = 0)
    (hind : ∀ (t : K) (μ : ι3 → K), lam' ≠ t • lam + μ ᵥ* C.d2) :
    ¬ Nonempty (Contraction (C.aug z lam hz hlam).toBased) := by
  rintro ⟨h⟩
  let r : (ι0 ⊕ Unit) ⊕ ι2 → K := Sum.elim 0 lam'
  have hdr : r ᵥ* (C.aug z lam hz hlam).toBased.dEO = 0 := by
    funext k
    rcases k with k | (k | k)
    · have e := congrFun hlam' k
      simpa [FourCx.toBased, FourCx.aug, vecMul, dotProduct, Fintype.sum_sum_type, r] using e
    · simp [FourCx.toBased, FourCx.aug, vecMul, dotProduct, Fintype.sum_sum_type, r]
    · simp [FourCx.toBased, FourCx.aug, vecMul, dotProduct, Fintype.sum_sum_type, r]
  have e1 : r = (r ᵥ* h.hEO) ᵥ* (C.aug z lam hz hlam).toBased.dOE := by
    have e := congrArg (fun M => r ᵥ* M) h.htpy_E
    simp only [vecMul_add, vecMul_one, ← vecMul_vecMul, hdr, zero_vecMul, zero_add] at e
    exact e.symm
  set s := r ᵥ* h.hEO with hs
  clear_value s
  apply hind (s (Sum.inr (Sum.inr ()))) (fun b => s (Sum.inr (Sum.inl b)))
  funext j
  have e := congrFun e1 (Sum.inr j)
  have e' : r (Sum.inr j) = lam' j := rfl
  rw [e'] at e
  rw [e]
  simp [FourCx.toBased, FourCx.aug, vecMul, dotProduct, Fintype.sum_sum_type]
  ring

/-- **The coordinate is additive in the cycle** (tex 3877–3892: `[z] ↦ [z] ⊗ [λ]` is linear):
`kmCoord(z₁ + z₂, λ) = kmCoord(z₁, λ) + kmCoord(z₂, λ)`. If one class is a multiple of the other
this is the homogeneity and the class invariance; otherwise all three coordinates vanish. Kind:
PROVED. -/
theorem kmCoord_add_z {z₁ z₂ : ι1 → K} {lam : ι2 → K} (h₁ : C.d1 *ᵥ z₁ = 0)
    (h₂ : C.d1 *ᵥ z₂ = 0) (h₁₂ : C.d1 *ᵥ (z₁ + z₂) = 0) (hlam : lam ᵥ* C.d1 = 0) :
    kmCoord C (z₁ + z₂) lam h₁₂ hlam σ =
      kmCoord C z₁ lam h₁ hlam σ + kmCoord C z₂ lam h₂ hlam σ := by
  by_cases hA : ∃ (t : K) (w : ι0 → K), z₂ = t • z₁ + C.d0 *ᵥ w
  · obtain ⟨t, w, hw⟩ := hA
    have e12 := kmCoord_congr C h₁₂ (cycle_add_boundary C (cycle_smul C h₁ (1 + t)) w) hlam hlam
      (by rw [hw, add_smul, one_smul, add_assoc]) rfl σ
    have e2 := kmCoord_congr C h₂ (cycle_add_boundary C (cycle_smul C h₁ t) w) hlam hlam hw rfl σ
    rw [e12, e2, kmCoord_add_boundary C (cycle_smul C h₁ (1 + t)) hlam σ w,
      kmCoord_add_boundary C (cycle_smul C h₁ t) hlam σ w, kmCoord_smul_z C h₁ hlam σ (1 + t),
      kmCoord_smul_z C h₁ hlam σ t]
    ring
  by_cases hB : ∃ (t : K) (w : ι0 → K), z₁ = t • z₂ + C.d0 *ᵥ w
  · obtain ⟨t, w, hw⟩ := hB
    have e12 := kmCoord_congr C h₁₂ (cycle_add_boundary C (cycle_smul C h₂ (t + 1)) w) hlam hlam
      (by rw [hw, add_smul, one_smul, add_right_comm]) rfl σ
    have e1 := kmCoord_congr C h₁ (cycle_add_boundary C (cycle_smul C h₂ t) w) hlam hlam hw rfl σ
    rw [e12, e1, kmCoord_add_boundary C (cycle_smul C h₂ (t + 1)) hlam σ w,
      kmCoord_add_boundary C (cycle_smul C h₂ t) hlam σ w, kmCoord_smul_z C h₂ hlam σ (t + 1),
      kmCoord_smul_z C h₂ hlam σ t]
    ring
  simp only [not_exists] at hA hB
  have k1 := kmCoord_eq_zero_of_not C σ h₁ hlam
    (not_contraction_of_independent_z C h₁ hlam h₂ hA)
  have k2 := kmCoord_eq_zero_of_not C σ h₂ hlam
    (not_contraction_of_independent_z C h₂ hlam h₁ hB)
  have k12 := kmCoord_eq_zero_of_not C σ h₁₂ hlam
    (not_contraction_of_independent_z C h₁₂ hlam h₁ (by
      intro t w heq
      by_cases ht : t = 0
      · apply hB 0 w
        rw [heq, ht, zero_smul, zero_smul]
      · apply hA (t⁻¹ - 1) (-(t⁻¹) • w)
        funext i
        have e := congrFun heq i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mulVec_smul] at e ⊢
        linear_combination (-t⁻¹) * e - (z₁ i + z₂ i) * (mul_inv_cancel₀ ht)))
  rw [k1, k2, k12, add_zero]

/-- **The coordinate is additive in the functional**: `kmCoord(z, λ₁ + λ₂) = kmCoord(z, λ₁) +
kmCoord(z, λ₂)`. (tex 3877–3892) Kind: PROVED. -/
theorem kmCoord_add_lam {z : ι1 → K} {lam₁ lam₂ : ι2 → K} (hz : C.d1 *ᵥ z = 0)
    (h₁ : lam₁ ᵥ* C.d1 = 0) (h₂ : lam₂ ᵥ* C.d1 = 0) (h₁₂ : (lam₁ + lam₂) ᵥ* C.d1 = 0) :
    kmCoord C z (lam₁ + lam₂) hz h₁₂ σ =
      kmCoord C z lam₁ hz h₁ σ + kmCoord C z lam₂ hz h₂ σ := by
  by_cases hA : ∃ (t : K) (μ : ι3 → K), lam₂ = t • lam₁ + μ ᵥ* C.d2
  · obtain ⟨t, μ, hμ⟩ := hA
    have e12 := kmCoord_congr C hz hz h₁₂ (closed_add_coboundary C (closed_smul C h₁ (1 + t)) μ)
      rfl (by rw [hμ, add_smul, one_smul, add_assoc]) σ
    have e2 := kmCoord_congr C hz hz h₂ (closed_add_coboundary C (closed_smul C h₁ t) μ) rfl hμ σ
    rw [e12, e2, kmCoord_add_coboundary C hz (closed_smul C h₁ (1 + t)) σ μ,
      kmCoord_add_coboundary C hz (closed_smul C h₁ t) σ μ, kmCoord_smul_lam C hz h₁ σ (1 + t),
      kmCoord_smul_lam C hz h₁ σ t]
    ring
  by_cases hB : ∃ (t : K) (μ : ι3 → K), lam₁ = t • lam₂ + μ ᵥ* C.d2
  · obtain ⟨t, μ, hμ⟩ := hB
    have e12 := kmCoord_congr C hz hz h₁₂ (closed_add_coboundary C (closed_smul C h₂ (t + 1)) μ)
      rfl (by rw [hμ, add_smul, one_smul, add_right_comm]) σ
    have e1 := kmCoord_congr C hz hz h₁ (closed_add_coboundary C (closed_smul C h₂ t) μ) rfl hμ σ
    rw [e12, e1, kmCoord_add_coboundary C hz (closed_smul C h₂ (t + 1)) σ μ,
      kmCoord_add_coboundary C hz (closed_smul C h₂ t) σ μ, kmCoord_smul_lam C hz h₂ σ (t + 1),
      kmCoord_smul_lam C hz h₂ σ t]
    ring
  simp only [not_exists] at hA hB
  have k1 := kmCoord_eq_zero_of_not C σ hz h₁
    (not_contraction_of_independent_lam C hz h₁ h₂ hA)
  have k2 := kmCoord_eq_zero_of_not C σ hz h₂
    (not_contraction_of_independent_lam C hz h₂ h₁ hB)
  have k12 := kmCoord_eq_zero_of_not C σ hz h₁₂
    (not_contraction_of_independent_lam C hz h₁₂ h₁ (by
      intro t μ heq
      by_cases ht : t = 0
      · apply hB 0 μ
        rw [heq, ht, zero_smul, zero_smul]
      · apply hA (t⁻¹ - 1) (-(t⁻¹) • μ)
        funext j
        have e := congrFun heq j
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, smul_vecMul] at e ⊢
        linear_combination (-t⁻¹) * e - (lam₁ j + lam₂ j) * (mul_inv_cancel₀ ht)))
  rw [k1, k2, k12, add_zero]

end Additive

/-! ### The coordinate as a bilinear form -/

section Bilinear

variable {K : Type} [Field K] {ι0 ι1 ι2 ι3 : Type} [Fintype ι0] [Fintype ι1] [Fintype ι2]
  [Fintype ι3] [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3]
  (C : FourCx K ι0 ι1 ι2 ι3) (σ : (ι0 ⊕ Unit) ⊕ ι2 ≃ ι1 ⊕ (ι3 ⊕ Unit))

/-- The cycles of `C¹`. (tex 3877–3892) Kind: definition. -/
abbrev cyclesOne : Submodule K (ι1 → K) := LinearMap.ker (Matrix.mulVecLin C.d1)

/-- The closed functionals on `C²`. (tex 3877–3892) Kind: definition. -/
abbrev closedTwo : Submodule K (ι2 → K) := LinearMap.ker (Matrix.vecMulLinear C.d1)

omit [Fintype ι0] [Fintype ι3] [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2]
  [DecidableEq ι3] in
/-- A cycle satisfies the cycle condition. (tex 3877–3892) Kind: PROVED. -/
theorem cyclesOne_cond (z : cyclesOne C) : C.d1 *ᵥ (z : ι1 → K) = 0 :=
  LinearMap.mem_ker.mp z.2

omit [Fintype ι0] [Fintype ι3] [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2]
  [DecidableEq ι3] in
/-- A closed functional satisfies the closedness condition. (tex 3877–3892) Kind: PROVED. -/
theorem closedTwo_cond (lam : closedTwo C) : (lam : ι2 → K) ᵥ* C.d1 = 0 :=
  LinearMap.mem_ker.mp lam.2

/-- **The Knudsen–Mumford coordinate as a bilinear form** on cycles and closed functionals
(tex 3877–3892: `(z, λ) ↦` the coordinate of `[z] ⊗ [λ]` in `det⁻¹ C ≅ H¹ ⊗ (H²)^*`).
Kind: definition (PROVED bilinearity). -/
def kmCoordBilin : cyclesOne C →ₗ[K] closedTwo C →ₗ[K] K :=
  LinearMap.mk₂ K (fun z lam => kmCoord C z lam (cyclesOne_cond C z) (closedTwo_cond C lam) σ)
    (fun _ _ _ => kmCoord_add_z C σ _ _ _ _)
    (fun c _ _ => kmCoord_smul_z C _ _ σ c)
    (fun _ _ _ => kmCoord_add_lam C σ _ _ _ _)
    (fun c _ _ => kmCoord_smul_lam C _ _ σ c)

/-- Evaluation of the bilinear form. (tex 3877–3892) Kind: PROVED (definitional). -/
theorem kmCoordBilin_apply (z : cyclesOne C) (lam : closedTwo C) :
    kmCoordBilin C σ z lam = kmCoord C z lam (cyclesOne_cond C z) (closedTwo_cond C lam) σ :=
  rfl

end Bilinear

/-- **Non-vacuity**: on `K --1--> K --0--> K --1--> K` the bilinear form is `(a, b) ↦ a b`, in
particular nonzero. (tex 3877–3892) Kind: PROVED. -/
theorem kmCoord_twoTerm_smul_example {K : Type} [Field K] (a b : K) :
    kmCoord (twoTerm (0 : Matrix (Fin 1) (Fin 1) K)) (a • 1) (b • 1)
      (cycle_smul _ twoTerm_zero_hz a) (closed_smul _ twoTerm_zero_hw b) (σ₀ 1) = a * b := by
  rw [kmCoord_smul_smul _ twoTerm_zero_hz twoTerm_zero_hw (σ₀ 1) a b, kmCoord_twoTerm_example,
    mul_one]

/-! ### The step of the support triangle -/

section Step

variable {K : Type} [Field K] {C : FullPreComplex K} (hB : IsUnit C.B.det)

/-- **The cancellation step with the coordinate change of the support triangle** (tex 4157–4194,
5509–5516): for a cycle `z` and a closed functional `λ` of the pre-cancellation complex whose
restrictions to the remaining complex are `e • z_P` and `e • λ_P` (the norm identity
`z_R = e_q i(z_P)` and `λ_R ∘ i = e_q λ_P`),
`kmCoord(C, z, λ) = det(B)⁻¹ · e² · kmCoord(C.cancel, z_P, λ_P)`. Kind: PROVED (from
`kmCoord_fullCancel` and the bihomogeneity). -/
theorem kmCoord_fullCancel_step {z : C.D1 ⊕ C.N → K} {lam : C.D2 ⊕ C.N → K}
    (hz : C.toFour.d1 *ᵥ z = 0) (hlam : lam ᵥ* C.toFour.d1 = 0) {zP : C.D1 → K}
    {lamP : C.D2 → K} (hzP : (C.cancel hB).toFour.d1 *ᵥ zP = 0)
    (hlamP : lamP ᵥ* (C.cancel hB).toFour.d1 = 0) (e : K) (hzR : z ∘ Sum.inl = e • zP)
    (hlamR : lam ∘ Sum.inl = e • lamP) :
    kmCoord C.toFour z lam hz hlam (σFull C.m0 C.m1 C.m2 C.N) =
      (C.B.det)⁻¹ * (e ^ 2 * kmCoord (C.cancel hB).toFour zP lamP hzP hlamP
        (σBlock C.m0 C.m1 C.m2)) := by
  have h1 : kmCoord (C.cancel hB).toFour (z ∘ Sum.inl) (lam ∘ Sum.inl)
      (FullPreComplex.hz_full hB hz) (FullPreComplex.hlam_full hB hlam) (σBlock C.m0 C.m1 C.m2) =
      kmCoord (C.cancel hB).toFour (e • zP) (e • lamP) (cycle_smul _ hzP e)
        (closed_smul _ hlamP e) (σBlock C.m0 C.m1 C.m2) :=
    kmCoord_congr _ _ _ _ _ hzR hlamR _
  have h2 := kmCoord_smul_smul (C.cancel hB).toFour hzP hlamP (σBlock C.m0 C.m1 C.m2) e e
  rw [kmCoord_fullCancel hB, h1]
  refine (congrArg (fun t => (C.B.det)⁻¹ * t) h2).trans ?_
  ring

/-- **(4.7) at one unused prime from the cancellation of the two-place singular block**
(tex 4157–4194, 4181–4184, 5509–5516): if the singular block of the pre-cancellation complex is
the two-place block `diag(z Fr_q − q, z⁻¹ Fr_q − q)` (`det B = q⁴ l_q`) of a Frobenius matrix with
trace `a_q` and determinant `q`, and the relaxed cycle and functional restrict to `e_q z_P`,
`e_q λ_P` (`e_q = a_q − z − z⁻¹`), then `l_q u_R = e_q² q⁻⁴ u_P` for the Knudsen–Mumford
coordinates `u_R = kmCoord(C, z, λ)` and `u_P = kmCoord(C.cancel, z_P, λ_P)`. Kind: PROVED. -/
theorem kmCoord_step_47 (F : Matrix (Fin 2) (Fin 2) K) (q qi a zq zqi : K) (hq : q * qi = 1)
    (ha : F.trace = a) (hd : F.det = q)
    (hBe : ∃ e : C.N ≃ Fin 2 ⊕ Fin 2, C.B = (twoPlaceBlock F q zq zqi).submatrix e e)
    {z : C.D1 ⊕ C.N → K} {lam : C.D2 ⊕ C.N → K} (hz : C.toFour.d1 *ᵥ z = 0)
    (hlam : lam ᵥ* C.toFour.d1 = 0) {zP : C.D1 → K} {lamP : C.D2 → K}
    (hzP : (C.cancel hB).toFour.d1 *ᵥ zP = 0) (hlamP : lamP ᵥ* (C.cancel hB).toFour.d1 = 0)
    (hzR : z ∘ Sum.inl = pointFactor a zq zqi • zP)
    (hlamR : lam ∘ Sum.inl = pointFactor a zq zqi • lamP) :
    quotientFactor F qi zq zqi * kmCoord C.toFour z lam hz hlam (σFull C.m0 C.m1 C.m2 C.N) =
      pointFactor a zq zqi ^ 2 * qi ^ 4 *
        kmCoord (C.cancel hB).toFour zP lamP hzP hlamP (σBlock C.m0 C.m1 C.m2) := by
  obtain ⟨e, hBeq⟩ := hBe
  have hdet : C.B.det = quotientDet F q zq zqi := by
    rw [hBeq, det_submatrix_equiv_self, det_twoPlaceBlock]
  have h := kmCoord_fullCancel_step hB hz hlam hzP hlamP (pointFactor a zq zqi) hzR hlamR
  have htri : C.B.det * kmCoord C.toFour z lam hz hlam (σFull C.m0 C.m1 C.m2 C.N) =
      pointFactor a zq zqi ^ 2 * 1 *
        kmCoord (C.cancel hB).toFour zP lamP hzP hlamP (σBlock C.m0 C.m1 C.m2) := by
    rw [h, ← mul_assoc, mul_inv_cancel₀ hB.ne_zero, one_mul, mul_one]
  have h47 := ZInQ.Manuscript.RC.Central.single_prime_47 (δ := C.B.det)
    (l := quotientFactor F qi zq zqi) hq (hdet.trans (quotientDet_eq zq zqi hq ha hd)) htri
  rw [h47]
  ring

end Step

/-! ### The support-triangle step in torsion coordinates, and the multi-prime (4.7) -/

section Steps

variable {K : Type} [Field K]

/-- **One relaxation step of the support triangle in torsion coordinates** (tex 4157–4194): the
relaxed coordinate `u_R` and the primitive coordinate `u_P` are the Knudsen–Mumford coordinates of
a pre-cancellation complex `C` (the relaxed model, `C_P ⊕ Q_q` with the two-place singular block
`B`, tex 5398–5424) and of its cancellation (the primitive model), at a relaxed cycle and functional
whose restrictions to the primitive model are `e_q z_P` and `e_q λ_P` (the norm identity and
`λ_R ∘ i = e_q λ_P`). Kind: definition (hypothesis shape; the replacement of the matrix-level
`NaturalStep` by the torsion-level step). -/
def KmStep (F : Matrix (Fin 2) (Fin 2) K) (q a zq zqi uR uP : K) : Prop :=
  ∃ (C : FullPreComplex K) (hB : IsUnit C.B.det)
    (_ : ∃ e : C.N ≃ Fin 2 ⊕ Fin 2, C.B = (twoPlaceBlock F q zq zqi).submatrix e e)
    (z : C.D1 ⊕ C.N → K) (lam : C.D2 ⊕ C.N → K) (hz : C.toFour.d1 *ᵥ z = 0)
    (hlam : lam ᵥ* C.toFour.d1 = 0) (zP : C.D1 → K) (lamP : C.D2 → K)
    (hzP : (C.cancel hB).toFour.d1 *ᵥ zP = 0) (hlamP : lamP ᵥ* (C.cancel hB).toFour.d1 = 0),
    z ∘ Sum.inl = pointFactor a zq zqi • zP ∧ lam ∘ Sum.inl = pointFactor a zq zqi • lamP ∧
      uR = kmCoord C.toFour z lam hz hlam (σFull C.m0 C.m1 C.m2 C.N) ∧
      uP = kmCoord (C.cancel hB).toFour zP lamP hzP hlamP (σBlock C.m0 C.m1 C.m2)

/-- **(4.7) at one step from a torsion-level step**: `l_q u_R = e_q² q⁻⁴ u_P`.
(tex 3877–3892) Kind: PROVED. -/
theorem KmStep.h47 {F : Matrix (Fin 2) (Fin 2) K} {q qi a zq zqi uR uP : K} (hq : q * qi = 1)
    (ha : F.trace = a) (hd : F.det = q) (h : KmStep F q a zq zqi uR uP) :
    quotientFactor F qi zq zqi * uR = pointFactor a zq zqi ^ 2 * qi ^ 4 * uP := by
  obtain ⟨C, hB, hBe, z, lam, hz, hlam, zP, lamP, hzP, hlamP, hzR, hlamR, hR, hP⟩ := h
  rw [hR, hP]
  exact kmCoord_step_47 hB F q qi a zq zqi hq ha hd hBe hz hlam hzP hlamP hzR hlamR

/-- **The multi-prime (4.7) from torsion-level steps** (tex 4166–4193, 4185–4188, 4222): if every
relaxation step `T → T ∪ {p}` (`p ∈ U \ T`) is a `KmStep`, then
`(∏_{p ∈ U} l_p) u_rel = (∏_{p ∈ U} e_p² q_p⁻⁴) u_prim` with `u_rel = u U`, `u_prim = u ∅`.
Kind: PROVED (from `KmStep.h47` and `prod_relax`). -/
theorem h47_of_kmSteps {ι : Type} [DecidableEq ι] (U : Finset ι)
    (F : ι → Matrix (Fin 2) (Fin 2) K) (q qi a zq zqi : ι → K) (u : Finset ι → K)
    (hq : ∀ p ∈ U, q p * qi p = 1) (ha : ∀ p ∈ U, (F p).trace = a p)
    (hd : ∀ p ∈ U, (F p).det = q p)
    (hstep : ∀ T ⊆ U, ∀ p ∈ U, p ∉ T →
      KmStep (F p) (q p) (a p) (zq p) (zqi p) (u (insert p T)) (u T)) :
    (∏ p ∈ U, quotientFactor (F p) (qi p) (zq p) (zqi p)) * u U =
      (∏ p ∈ U, pointFactor (a p) (zq p) (zqi p) ^ 2 * qi p ^ 4) * u ∅ :=
  ZInQ.Manuscript.RC.Central.prod_relax U (fun p => quotientFactor (F p) (qi p) (zq p) (zqi p))
    (fun p => pointFactor (a p) (zq p) (zqi p)) (fun p => qi p ^ 4) u
    (fun T hT p hp hpT => (hstep T hT p hp hpT).h47 (hq p hp) (ha p hp) (hd p hp))

/-- **Descent of the multi-prime (4.7) from the fraction field** (tex 4166–4193): the models of
the support triangle live over the fraction field `F` of the coefficient domain `R`; an identity
among images of elements of `R` holds in `R`. Kind: PROVED. -/
theorem h47_descend {R F : Type} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] {ι : Type} (U : Finset ι) (l e ε : ι → R) (urel uprim : R)
    (h : (∏ p ∈ U, algebraMap R F (l p)) * algebraMap R F urel =
      (∏ p ∈ U, algebraMap R F (e p) ^ 2 * algebraMap R F (ε p)) * algebraMap R F uprim) :
    (∏ p ∈ U, l p) * urel = (∏ p ∈ U, e p ^ 2 * ε p) * uprim := by
  apply IsFractionRing.injective R F
  simpa only [map_mul, map_prod, map_pow] using h

/-- The two-place quotient factor as a polynomial in the trace and the determinant:
`l_q = (1 − q⁻¹ z a_q + q⁻² z² q)(1 − q⁻¹ z⁻¹ a_q + q⁻² z⁻² q)` (tex 4208–4210).
Kind: PROVED. -/
theorem quotientFactor_eq_poly {R : Type} [CommRing R] {F : Matrix (Fin 2) (Fin 2) R}
    {q qi a z zi : R} (ha : F.trace = a) (hd : F.det = q) :
    quotientFactor F qi z zi =
      (1 - qi * z * a + (qi * z) ^ 2 * q) * (1 - qi * zi * a + (qi * zi) ^ 2 * q) := by
  unfold quotientFactor
  rw [det_one_sub_smul, det_one_sub_smul, ha, hd]

/-- **The multi-prime (4.7) over the coefficient domain from torsion-level steps over its fraction
field** (tex 4166–4193): the leaf-shaped identity `(∏_U l_p) u_rel = (∏_U e_p² q_p⁻⁴) u_prim` over
`Λ`, when every relaxation step is a `KmStep` over `Frac Λ` (for a Frobenius matrix over `Frac Λ`
with the trace and determinant of `F p`). Kind: PROVED. -/
theorem h47_of_kmSteps_descend {Λ Fr : Type} [CommRing Λ] [IsDomain Λ] [Field Fr] [Algebra Λ Fr]
    [IsFractionRing Λ Fr] {ι : Type} [DecidableEq ι] (U : Finset ι)
    (F : ι → Matrix (Fin 2) (Fin 2) Λ) (q qi a z zi : ι → Λ) (u : Finset ι → Λ)
    (hq : ∀ p ∈ U, q p * qi p = 1) (ha : ∀ p ∈ U, (F p).trace = a p)
    (hd : ∀ p ∈ U, (F p).det = q p)
    (hstep : ∀ T ⊆ U, ∀ p ∈ U, p ∉ T → ∃ F' : Matrix (Fin 2) (Fin 2) Fr,
      F'.trace = algebraMap Λ Fr (a p) ∧ F'.det = algebraMap Λ Fr (q p) ∧
      KmStep F' (algebraMap Λ Fr (q p)) (algebraMap Λ Fr (a p)) (algebraMap Λ Fr (z p))
        (algebraMap Λ Fr (zi p)) (algebraMap Λ Fr (u (insert p T))) (algebraMap Λ Fr (u T))) :
    (∏ p ∈ U, quotientFactor (F p) (qi p) (z p) (zi p)) * u U =
      (∏ p ∈ U, pointFactor (a p) (z p) (zi p) ^ 2 * qi p ^ 4) * u ∅ := by
  apply h47_descend (F := Fr) U (fun p => quotientFactor (F p) (qi p) (z p) (zi p))
    (fun p => pointFactor (a p) (z p) (zi p)) (fun p => qi p ^ 4) (u U) (u ∅)
  refine ZInQ.Manuscript.RC.Central.prod_relax U
    (fun p => algebraMap Λ Fr (quotientFactor (F p) (qi p) (z p) (zi p)))
    (fun p => algebraMap Λ Fr (pointFactor (a p) (z p) (zi p)))
    (fun p => algebraMap Λ Fr (qi p ^ 4)) (fun T => algebraMap Λ Fr (u T)) ?_
  intro T hT p hp hpT
  obtain ⟨F', htr, hdet, hK⟩ := hstep T hT p hp hpT
  have hq' : algebraMap Λ Fr (q p) * algebraMap Λ Fr (qi p) = 1 := by
    rw [← map_mul, hq p hp, map_one]
  have h := hK.h47 hq' htr hdet
  have e1 : quotientFactor F' (algebraMap Λ Fr (qi p)) (algebraMap Λ Fr (z p))
      (algebraMap Λ Fr (zi p)) = algebraMap Λ Fr (quotientFactor (F p) (qi p) (z p) (zi p)) := by
    rw [quotientFactor_eq_poly htr hdet, quotientFactor_eq_poly (ha p hp) (hd p hp)]
    simp only [map_mul, map_sub, map_add, map_pow, map_one]
  have e2 : pointFactor (algebraMap Λ Fr (a p)) (algebraMap Λ Fr (z p))
      (algebraMap Λ Fr (zi p)) = algebraMap Λ Fr (pointFactor (a p) (z p) (zi p)) := by
    simp only [pointFactor, map_sub]
  rw [e1, e2] at h
  rw [h, map_pow]

end Steps

/-! ### Non-vacuity of the torsion-level step -/

section Example

/-- The two-place singular block of the example: `F = 1`, `q = 1`, `z = z⁻¹ = 2`.
(tex 3877–3892, 5398–5424) Kind:
definition. -/
abbrev exB : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ := twoPlaceBlock 1 1 2 2

/-- The example block is invertible (`det = 1`). (tex 3877–3892, 5398–5424) Kind: PROVED. -/
theorem exB_det : exB.det = 1 := by
  rw [det_twoPlaceBlock]
  simp [quotientDet, det_fin_two]
  norm_num

/-- **An explicit pre-cancellation complex** `K --0--> K` in degrees one and two with the
two-place block `N --B--> N` (tex 5398–5424): all old blocks empty or zero. Kind: definition. -/
def exFull : FullPreComplex ℚ where
  m0 := 0
  m1 := 0
  m2 := 0
  N := Fin 2 ⊕ Fin 2
  c0 := 0
  Y := 0
  P := 0
  Q := 0
  T := 0
  B := exB
  U := 0
  V := 0
  c1_c0 := by
    ext _ j
    exact j.elim0
  c2_c1 := by
    ext i _
    exact i.elim0

/-- The singular block of the example is a unit. (tex 3877–3892, 5398–5424) Kind: PROVED. -/
theorem exFull_hB : IsUnit exFull.B.det := by
  change IsUnit exB.det
  rw [exB_det]
  exact isUnit_one

/-- The relaxed cycle of the example is a cycle. (tex 5398–5424) Kind: PROVED. -/
theorem exFull_hz : exFull.toFour.d1 *ᵥ (Sum.elim (pointFactor (2 : ℚ) 2 2 • 1) 0) = 0 := by
  change fromBlocks (0 : Matrix exFull.D2 exFull.D1 ℚ) 0 0 exB *ᵥ
    (Sum.elim (pointFactor (2 : ℚ) 2 2 • 1) 0) = 0
  rw [fromBlocks_mulVec]
  simp

/-- The relaxed functional of the example is closed. (tex 5398–5424) Kind: PROVED. -/
theorem exFull_hlam : (Sum.elim (pointFactor (2 : ℚ) 2 2 • 1) 0) ᵥ* exFull.toFour.d1 = 0 := by
  change (Sum.elim (pointFactor (2 : ℚ) 2 2 • 1) 0) ᵥ*
    fromBlocks (0 : Matrix exFull.D2 exFull.D1 ℚ) 0 0 exB = 0
  rw [vecMul_fromBlocks]
  simp

/-- The primitive cycle of the example is a cycle. (tex 5398–5424) Kind: PROVED. -/
theorem exFull_hzP : (exFull.cancel exFull_hB).toFour.d1 *ᵥ (1 : exFull.D1 → ℚ) = 0 := by
  change ((0 : Matrix exFull.D2 exFull.D1 ℚ) - (0 : Matrix exFull.D2 exFull.N ℚ) *
    exFull.B⁻¹ * (0 : Matrix exFull.N exFull.D1 ℚ)) *ᵥ (1 : exFull.D1 → ℚ) = 0
  simp

/-- The primitive functional of the example is closed. (tex 5398–5424) Kind: PROVED. -/
theorem exFull_hlamP : (1 : exFull.D2 → ℚ) ᵥ* (exFull.cancel exFull_hB).toFour.d1 = 0 := by
  change (1 : exFull.D2 → ℚ) ᵥ* ((0 : Matrix exFull.D2 exFull.D1 ℚ) -
    (0 : Matrix exFull.D2 exFull.N ℚ) * exFull.B⁻¹ * (0 : Matrix exFull.N exFull.D1 ℚ)) = 0
  simp

/-- **The step of the example** (tex 4157–4194, 5398–5424). Kind: PROVED. -/
theorem exFull_kmStep : KmStep (1 : Matrix (Fin 2) (Fin 2) ℚ) 1 2 2 2
    (kmCoord exFull.toFour _ _ exFull_hz exFull_hlam
      (σFull exFull.m0 exFull.m1 exFull.m2 exFull.N))
    (kmCoord (exFull.cancel exFull_hB).toFour 1 1 exFull_hzP exFull_hlamP
      (σBlock exFull.m0 exFull.m1 exFull.m2)) :=
  ⟨exFull, exFull_hB, ⟨Equiv.refl (Fin 2 ⊕ Fin 2), rfl⟩, _, _, exFull_hz, exFull_hlam, 1, 1,
    exFull_hzP, exFull_hlamP, Sum.elim_comp_inl _ _, Sum.elim_comp_inl _ _, rfl, rfl⟩

/-- **The primitive coordinate of the example is `−1`** (Elliot's block computation
`kmCoord_block`: no Smith blocks, remaining map `H₁ → H₂` zero, `α = β = 1`).
(tex 3877–3892, 5545–5595) Kind: PROVED. -/
theorem exFull_uP : kmCoord (exFull.cancel exFull_hB).toFour 1 1 exFull_hzP exFull_hlamP
    (σBlock exFull.m0 exFull.m1 exFull.m2) = -1 := by
  have e0 : IsEmpty (Fin (exFull.cancel exFull_hB).m0) := inferInstanceAs (IsEmpty (Fin 0))
  have e1 : IsEmpty (Fin (exFull.cancel exFull_hB).m1) := inferInstanceAs (IsEmpty (Fin 0))
  have e2 : IsEmpty (Fin (exFull.cancel exFull_hB).m2) := inferInstanceAs (IsEmpty (Fin 0))
  have h0 : IsUnit (exFull.cancel exFull_hB).A0.det := by
    rw [Matrix.det_isEmpty]; exact isUnit_one
  have h1 : IsUnit (exFull.cancel exFull_hB).A1.det := by
    rw [Matrix.det_isEmpty]; exact isUnit_one
  have h2 : IsUnit (exFull.cancel exFull_hB).A2.det := by
    rw [Matrix.det_isEmpty]; exact isUnit_one
  have hb := kmCoord_block (D := exFull.cancel exFull_hB) 1 1 exFull_hzP exFull_hlamP h0 h1 h2
  refine hb.trans ?_
  have hR : (exFull.cancel exFull_hB).hRem = 0 := by
    simp [BlockComplex.hRem, exFull, FullPreComplex.cancel, dotProduct]
  have hα : (exFull.cancel exFull_hB).alphaB 1 = 1 := by
    simp [BlockComplex.alphaB, dotProduct]
  have hβ : (exFull.cancel exFull_hB).betaB 1 = 1 := by
    simp [BlockComplex.betaB, dotProduct]
  simp only [hR, ite_true, hα, hβ, Matrix.det_isEmpty]
  norm_num

/-- **The relaxed coordinate of the example is `−4`**, from the step relation
`u_R = det(B)⁻¹ e_q² u_P` with `det B = 1`, `e_q = −2`, `u_P = −1`: the step is not degenerate.
(tex 4157–4194, 5509–5516) Kind: PROVED. -/
theorem exFull_uR : kmCoord exFull.toFour _ _ exFull_hz exFull_hlam
    (σFull exFull.m0 exFull.m1 exFull.m2 exFull.N) = -4 := by
  refine (kmCoord_fullCancel_step exFull_hB exFull_hz exFull_hlam exFull_hzP exFull_hlamP
    (pointFactor 2 2 2) (Sum.elim_comp_inl _ _) (Sum.elim_comp_inl _ _)).trans ?_
  refine (congrArg (fun t => exFull.B.det⁻¹ * (pointFactor (2 : ℚ) 2 2 ^ 2 * t)) exFull_uP).trans ?_
  change (exB.det)⁻¹ * _ = _
  rw [exB_det]
  simp [pointFactor]
  norm_num

/-- **Non-vacuity of `KmStep`, with nonzero coordinates**: the example is a torsion-level step
for `F = 1`, `q = 1`, `a = 2`, `z = z⁻¹ = 2`, with `u_R = −4`, `u_P = −1`, and its (4.7) reads
`l_q u_R = e_q² u_P`. (tex 4157–4194) Kind: PROVED. -/
theorem kmStep_example :
    KmStep (1 : Matrix (Fin 2) (Fin 2) ℚ) 1 2 2 2 (-4) (-1) ∧
      quotientFactor 1 1 2 2 * (-4) = pointFactor 2 2 2 ^ 2 * 1 ^ 4 * (-1 : ℚ) := by
  have h := exFull_kmStep
  rw [exFull_uR, exFull_uP] at h
  exact ⟨h, h.h47 (by norm_num) (by simp) (by simp)⟩

end Example

end ZInQ.Manuscript.RC.Wiring

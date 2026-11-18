import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.NewLocalCancel
import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.CoordParam
import ZInQKernel.Contrib.CloudB3RC53.SelmerDuality.SupportChange

/-!
# The identification from the new-local model and the support change

Manuscript `diophantine_zq.tex`, proof of Lemma `ex:limits-fixed-field-budget`, tex L5394–5425,
and of Proposition `ex:limits-fixed-field-clearing`, tex L5509–5535.

The single identification `SelmerIdentification` stated its augmentation, pole and budget fields
directly about the remaining complex `D`. Here they are DERIVED from data in the shape of the
manuscript's construction, phrased against lane SelmerDuality's `SupportChangeData`:

* `PreComplex.map`, `PreComplex.old`, `PreComplex.oldIncl`: coefficient change of a pre-cancellation
  complex; when `Y = T = 0` (upper triangular: the old summands form a subcomplex), the old part
  and its inclusion (a chain map);
* `NewLocalModel b dK hK cE tK` (GLUE; every field is a statement about the finite free model or a
  Selmer-complex comparison):
  - a pre-cancellation complex `C` over `Λ[G]` (tex 5394, 5414–5420: "All matrices and their
    inverses at this step lie in `Λ[G]`"), whose new local block augments to the block diagonal of
    new local blocks `A_q` with `det A_q = t^{d_q} v_q + 2w_q`, `d_q ≤ 4` (tex 5420–5430), with
    `T₀ = 0` and `Y₀ = 0` (tex 5421: `B₀ = A`, `T₀ = 0`; the old part is a subcomplex of the upper
    triangular model, tex 5399–5401, 5238);
  - the augmented old part is in central Smith form (tex 5522–5532: "centrally the only nonzero
    differentials are the Smith disks") with nonzero Smith entries, and the (5.7) counts hold for
    its Smith data (tex 5355–5392);
  - the family Selmer complex: Selmer data `sel` over `𝒪[G]` and a quasi-isomorphism from `C ⊗ 𝒪[G]`
    to its Selmer complex (tex 5394–5397: "`C` the retained finite free family model");
  - the support-change triangle (5.6) at augmentation (tex 5236–5240, 5397–5403): support-change data
    `sc` over `Λ`, quasi-isomorphisms from the augmented `C` to `selCx sc.Dp` and from the augmented
    old part to `selCx sc.D`, commuting with the support comparison `supportMap sc`.
* `NewLocalModel.toSelmerIdentification` (PROVED): the remaining complex is the cancellation of the
  new local block over `𝒪[G]` (invertible: RC7's `matrix_isUnit_of_isUnit_aug` and
  `newLocal_family_pole_genuine`), and every field of `SelmerIdentification` follows: augmentation
  (`T₀ = 0`), poles (sign-evaluated Schur complements; adjacent differentials unchanged), budget
  (the old Smith data), and the quasi-isomorphism (`PreComplex.incl_quasiIso` composed with the
  family model).
* `clearingModel_of_newLocal` (PROVED): RC0's `ClearingModel` from `NewLocalModel` and E1 (with the
  coordinate parameter).

Not derived (interface gaps, recorded as ELLIOT): the identification of the augmentation of
`sel` with `sc.Dp` needs a coefficient-change interface for `SelData` (none exists); the central
counts (5.7) for the old Smith data are not derived from `sc`'s cohomology (RankCounts' central
complex is not linked to `selCx`); the new local quotient is not matched with
`SupportChangeUnramified` (that interface has one new place).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.ClearingComplex

open CategoryTheory Matrix
open ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Wiring
open ZInQ.Manuscript.RC.Determinant (Lam OO SignGroup SmithBlocks ScalarData aug sgnChar
  genuinePole)
open ZInQ.Contrib.CloudB3RC53.PairedFunctional

/-! ### Coefficient change and the old part of a pre-cancellation complex -/

namespace PreComplex

variable {S S' : Type} [CommRing S] [CommRing S']

/-- **Coefficient change** of a pre-cancellation complex along a ring map. -/
def map (C : PreComplex S) (f : S →+* S') : PreComplex S' where
  m0 := C.m0
  m1 := C.m1
  m2 := C.m2
  N := C.N
  c0 := C.c0.map f
  X := C.X.map f
  Y := C.Y.map f
  P := C.P.map f
  Q := C.Q.map f
  T := C.T.map f
  B := C.B.map f
  c1_c0 := by
    rw [← fromRows_map, ← Matrix.map_mul, C.c1_c0, Matrix.map_zero _ (map_zero f)]
  c2_c1 := by
    rw [← fromRows_map, ← fromBlocks_map, ← Matrix.map_mul, C.c2_c1,
      Matrix.map_zero _ (map_zero f)]

variable (C : PreComplex S)

/-- **The old part** of an upper triangular pre-cancellation complex (`Y = T = 0`): `d⁰ = c⁰`,
`d¹ = X`, `d² = P`. -/
def old (hY : C.Y = 0) (_hT : C.T = 0) : BlockComplex S where
  m0 := C.m0
  m1 := C.m1
  m2 := C.m2
  d0 := C.c0
  d1 := C.X
  d2 := C.P
  d1_d0 := C.X_c0
  d2_d1 := by
    have h := C.PX_QY
    rwa [hY, Matrix.mul_zero, add_zero] at h

variable {C}

/-- The components of the inclusion of the old part. -/
def oinc (hY : C.Y = 0) (hT : C.T = 0) : (i : ℤ) → ((C.old hY hT).idx i → S) →ₗ[S] (C.idx i → S)
  | 0 => LinearMap.id
  | 1 => LinearMap.id
  | 2 => (fromRows (1 : Matrix (Fin C.m1 ⊕ Unit ⊕ Fin C.m2) (Fin C.m1 ⊕ Unit ⊕ Fin C.m2) S)
      (0 : Matrix C.N (Fin C.m1 ⊕ Unit ⊕ Fin C.m2) S)).mulVecLin
  | 3 => (fromRows (1 : Matrix (Fin C.m2) (Fin C.m2) S) (0 : Matrix C.N (Fin C.m2) S)).mulVecLin
  | _ => 0

theorem oinc_comm (hY : C.Y = 0) (hT : C.T = 0) (i : ℤ) (x : (C.old hY hT).idx i → S) :
    oinc hY hT (i + 1) ((C.old hY hT).ddL i x) = C.ddL i (oinc hY hT i x) := by
  match i with
  | 0 => rfl
  | 1 =>
    have hM : fromRows (1 : Matrix (Fin C.m1 ⊕ Unit ⊕ Fin C.m2) (Fin C.m1 ⊕ Unit ⊕ Fin C.m2) S)
        (0 : Matrix C.N (Fin C.m1 ⊕ Unit ⊕ Fin C.m2) S) * C.X = fromRows C.X C.Y := by
      rw [fromRows_mul, Matrix.one_mul, Matrix.zero_mul, hY]
    have h : ∀ y : Fin C.m0 ⊕ Unit ⊕ Fin C.m1 → S,
        (fromRows (1 : Matrix (Fin C.m1 ⊕ Unit ⊕ Fin C.m2) (Fin C.m1 ⊕ Unit ⊕ Fin C.m2) S)
          (0 : Matrix C.N (Fin C.m1 ⊕ Unit ⊕ Fin C.m2) S)).mulVec (C.X.mulVec y) =
          (fromRows C.X C.Y).mulVec y := fun y => by
      rw [Matrix.mulVec_mulVec, hM]
    exact h x
  | 2 =>
    have hM : fromRows (1 : Matrix (Fin C.m2) (Fin C.m2) S) (0 : Matrix C.N (Fin C.m2) S) * C.P =
        fromBlocks C.P C.Q C.T C.B *
          fromRows (1 : Matrix (Fin C.m1 ⊕ Unit ⊕ Fin C.m2) (Fin C.m1 ⊕ Unit ⊕ Fin C.m2) S)
            (0 : Matrix C.N (Fin C.m1 ⊕ Unit ⊕ Fin C.m2) S) := by
      rw [fromRows_mul, fromBlocks_mul_fromRows, hT, Matrix.one_mul, Matrix.zero_mul,
        Matrix.mul_one, Matrix.mul_one, Matrix.mul_zero, Matrix.mul_zero, add_zero, add_zero]
    have h : ∀ y : Fin C.m1 ⊕ Unit ⊕ Fin C.m2 → S,
        (fromRows (1 : Matrix (Fin C.m2) (Fin C.m2) S) (0 : Matrix C.N (Fin C.m2) S)).mulVec
          (C.P.mulVec y) =
        (fromBlocks C.P C.Q C.T C.B).mulVec
          ((fromRows (1 : Matrix (Fin C.m1 ⊕ Unit ⊕ Fin C.m2) (Fin C.m1 ⊕ Unit ⊕ Fin C.m2) S)
            (0 : Matrix C.N (Fin C.m1 ⊕ Unit ⊕ Fin C.m2) S)).mulVec y) := fun y => by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM]
    exact h x
  | 3 => rfl
  | Int.ofNat (n + 4) => rfl
  | Int.negSucc n =>
    change oinc hY hT (Int.negSucc n + 1) 0 = 0
    exact map_zero _

/-- **The inclusion of the old part** (a chain map; the first map of (5.6)). -/
def oldIncl (hY : C.Y = 0) (hT : C.T = 0) : GHom (C.old hY hT).toGCx C.toGCx where
  f i j h := by subst h; exact oinc hY hT i
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj h₁
    exact oinc_comm hY hT i x

end PreComplex

/-! ### The coefficient rings -/

variable {b : ℕ}

/-- `Λ[G] → 𝒪[G]`. -/
abbrev φO (b : ℕ) : MonoidAlgebra Lam (SignGroup b) →+* MonoidAlgebra OO (SignGroup b) :=
  MonoidAlgebra.mapRingHom (SignGroup b) (algebraMap Lam OO)

/-- The augmentation `Λ[G] → Λ` as a ring map. -/
abbrev augR (b : ℕ) : MonoidAlgebra Lam (SignGroup b) →+* Lam :=
  (aug (O := Lam) (G := SignGroup b)).toRingHom

/-- The augmentation `𝒪[G] → 𝒪` as a ring map. -/
abbrev augS (b : ℕ) : MonoidAlgebra OO (SignGroup b) →+* OO :=
  (aug (O := OO) (G := SignGroup b)).toRingHom

theorem signEval_φO (χ : SignGroup b →* ℤˣ) (r : MonoidAlgebra Lam (SignGroup b)) :
    Determinant.signEval χ (φO b r) = algebraMap Lam OO (Determinant.signEval χ r) := by
  have : ((Determinant.signEval (O := OO) χ).toRingHom).comp (φO b) =
      (algebraMap Lam OO).comp (Determinant.signEval (O := Lam) χ).toRingHom := by
    refine MonoidAlgebra.ringHom_ext (fun c => ?_) (fun g => ?_)
    · simp [Determinant.signEval_single]
    · simp [Determinant.signEval_single]
  exact congrArg (fun f => f r) this

theorem aug_φO (r : MonoidAlgebra Lam (SignGroup b)) :
    aug (φO b r) = algebraMap Lam OO (aug r) := by
  rw [← Determinant.signEval_sgnChar_zero, ← Determinant.signEval_sgnChar_zero, signEval_φO]

theorem map_φO_signEval {r c : Type} (M : Matrix r c (MonoidAlgebra Lam (SignGroup b)))
    (χ : SignGroup b →* ℤˣ) :
    (M.map (φO b)).map (Determinant.signEval χ) =
      (M.map (Determinant.signEval χ)).map (algebraMap Lam OO) := by
  exact Matrix.ext fun i j => signEval_φO χ (M i j)

theorem map_φO_aug {r c : Type} (M : Matrix r c (MonoidAlgebra Lam (SignGroup b))) :
    (M.map (φO b)).map (augS b) = (M.map (augR b)).map (algebraMap Lam OO) := by
  exact Matrix.ext fun i j => aug_φO (M i j)

/-- A ring map carries the inverse of an invertible matrix to the inverse. -/
theorem map_inv_of_isUnit {R R' n : Type} [CommRing R] [CommRing R'] [Fintype n] [DecidableEq n]
    (f : R →+* R') (A : Matrix n n R) (hA : IsUnit A.det) : (A⁻¹).map f = (A.map f)⁻¹ := by
  refine (Matrix.inv_eq_right_inv ?_).symm
  rw [← Matrix.map_mul, mul_nonsing_inv A hA, Matrix.map_one _ (map_zero f) (map_one f)]

/-! ### Invertibility of the new local block over `𝒪[G]` -/

/-- **The new local block is invertible over `𝒪[G]`** (PROVED; RC7's
`matrix_isUnit_of_isUnit_aug` and `newLocal_family_pole_genuine` at the trivial character). -/
theorem isUnit_B_of {Qn ιn : Type} [Fintype Qn] [DecidableEq Qn] [Fintype ιn] [DecidableEq ιn]
    (A : Qn → Matrix ιn ιn Lam) (dq : Qn → ℕ) (hd : ∀ q, dq q ≤ 4) (v : Qn → Lamˣ) (w : Qn → Lam)
    (hdet : ∀ q, (A q).det = (PowerSeries.X : Lam) ^ dq q * (v q : Lam) + 2 * w q)
    (C : PreComplex (MonoidAlgebra Lam (SignGroup b))) (eN : C.N ≃ ιn × Qn)
    (hB0 : (C.B.submatrix eN.symm eN.symm).map aug = Matrix.blockDiagonal A) :
    IsUnit (C.map (φO b)).B.det := by
  rw [← Matrix.isUnit_iff_isUnit_det]
  refine Determinant.matrix_isUnit_of_isUnit_aug Determinant.isUnit_one_add_two_mul_OO
    Determinant.signGroup_mul_self _ ?_
  change IsUnit ((C.B.map (φO b)).map aug).det
  have h0 := (Determinant.newLocal_family_pole_genuine A dq hd v w hdet
    (C.B.submatrix eN.symm eN.symm) hB0 (sgnChar 0) 0).1
  have e : ((C.B.submatrix eN.symm eN.symm).map (Determinant.signEval (sgnChar 0))).map
      (algebraMap Lam OO) = ((C.B.map (φO b)).map aug).submatrix eN.symm eN.symm := by
    refine Matrix.ext fun i j => ?_
    change algebraMap Lam OO (Determinant.signEval (sgnChar 0) (C.B _ _)) = aug (φO b (C.B _ _))
    rw [Determinant.signEval_sgnChar_zero, aug_φO]
  rw [e, Matrix.det_submatrix_equiv_self] at h0
  exact h0

/-- **The remaining complex** of a pre-cancellation family model: the cancellation of the new local
block over `𝒪[G]`. -/
def remOf {Qn ιn : Type} [Fintype Qn] [DecidableEq Qn] [Fintype ιn] [DecidableEq ιn]
    (A : Qn → Matrix ιn ιn Lam) (dq : Qn → ℕ) (hd : ∀ q, dq q ≤ 4) (v : Qn → Lamˣ) (w : Qn → Lam)
    (hdet : ∀ q, (A q).det = (PowerSeries.X : Lam) ^ dq q * (v q : Lam) + 2 * w q)
    (C : PreComplex (MonoidAlgebra Lam (SignGroup b))) (eN : C.N ≃ ιn × Qn)
    (hB0 : (C.B.submatrix eN.symm eN.symm).map aug = Matrix.blockDiagonal A) :
    BlockComplex (MonoidAlgebra OO (SignGroup b)) :=
  (C.map (φO b)).cancel (isUnit_B_of A dq hd v w hdet C eN hB0)

/-! ### The new-local model -/

/-- **The new-local model of the family** (GLUE; see the module docstring). -/
structure NewLocalModel (b : ℕ) (dK hK cE tK : ℕ) where
  /-- the new places and the index of a local block -/
  Qn : Type
  ιn : Type
  [fQ : Fintype Qn]
  [dQ : DecidableEq Qn]
  [fι : Fintype ιn]
  [dι : DecidableEq ιn]
  /-- the new local blocks over `Λ` -/
  A : Qn → Matrix ιn ιn Lam
  dq : Qn → ℕ
  hd : ∀ q, dq q ≤ 4
  v : Qn → Lamˣ
  w : Qn → Lam
  hdet : ∀ q, (A q).det = (PowerSeries.X : Lam) ^ dq q * (v q : Lam) + 2 * w q
  /-- the pre-cancellation finite free family model over `Λ[G]` -/
  C : PreComplex (MonoidAlgebra Lam (SignGroup b))
  /-- its new local summands are indexed by the local blocks -/
  eN : C.N ≃ ιn × Qn
  /-- `B₀ = A = diag(A_q)` (tex 5421) -/
  hB0 : (C.B.submatrix eN.symm eN.symm).map aug = Matrix.blockDiagonal A
  /-- `T₀ = 0` (tex 5421) -/
  hT0 : C.T.map (augR b) = 0
  /-- `Y₀ = 0`: the old part is a subcomplex of the augmented model (tex 5238, 5399–5401) -/
  hY0 : C.Y.map (augR b) = 0
  /-- the central Smith entries of the augmented old part -/
  s : (i : ℕ) → Fin (((C.map (augR b)).old hY0 hT0).mi i) → ℤ_[2]
  s_ne : ∀ i j, s i j ≠ 0
  /-- the augmented old part is in central Smith form (tex 5522–5532) -/
  central : ∀ i, (((C.map (augR b)).old hY0 hT0).Ai i).map PowerSeries.constantCoeff =
    Matrix.diagonal (s i)
  /-- the (5.7) counts for the old Smith data (tex 5355–5392) -/
  budget : BudgetInputs ((remOf A dq hd v w hdet C eN hB0).toSmithBlocks (O := OO)
    ((C.map (augR b)).old hY0 hT0).Ai s s_ne central) dK hK cE tK
  /-- the family Selmer data over `𝒪[G]` -/
  sel : SelData (MonoidAlgebra OO (SignGroup b))
  /-- `C ⊗ 𝒪[G]` is a model of the family Selmer complex (tex 5394–5397) -/
  ψ : (C.map (φO b)).toGCx.toCC ⟶ (selCx sel).toCC
  qis : QuasiIso ψ
  /-- the support change at augmentation (5.6) -/
  sc : SelmerDuality.SupportChangeData Lam
  /-- the augmented `C` models the new-support Selmer complex -/
  ψ0 : (C.map (augR b)).toGCx.toCC ⟶ (selCx sc.Dp).toCC
  qis0 : QuasiIso ψ0
  /-- the augmented old part models the old-support Selmer complex -/
  ψold : ((C.map (augR b)).old hY0 hT0).toGCx.toCC ⟶ (selCx sc.D).toCC
  qisOld : QuasiIso ψold
  /-- compatibility with the support comparison -/
  square : ψold ≫ SelmerDuality.GHom.toCC (SelmerDuality.supportMap sc) =
    SelmerDuality.GHom.toCC ((C.map (augR b)).oldIncl hY0 hT0) ≫ ψ0

namespace NewLocalModel

attribute [instance] fQ dQ fι dι

variable {dK hK cE tK : ℕ} (M : NewLocalModel b dK hK cE tK)

/-- The new local block as a family over `ι × Q`. -/
abbrev Bsub : Matrix (M.ιn × M.Qn) (M.ιn × M.Qn) (MonoidAlgebra Lam (SignGroup b)) :=
  M.C.B.submatrix M.eN.symm M.eN.symm

theorem isUnit_B : IsUnit (M.C.map (φO b)).B.det :=
  isUnit_B_of M.A M.dq M.hd M.v M.w M.hdet M.C M.eN M.hB0

/-- **The remaining complex**: the cancellation of the new local block over `𝒪[G]`. -/
def D : BlockComplex (MonoidAlgebra OO (SignGroup b)) :=
  remOf M.A M.dq M.hd M.v M.w M.hdet M.C M.eN M.hB0

/-- The augmented old part over `Λ`. -/
abbrev oldC : BlockComplex Lam := (M.C.map (augR b)).old M.hY0 M.hT0

theorem d2_map_aug : M.D.d2.map (augS b) = (M.C.P.map (augR b)).map (algebraMap Lam OO) := by
  change (M.C.P.map (φO b) - M.C.Q.map (φO b) * (M.C.B.map (φO b))⁻¹ *
    M.C.T.map (φO b)).map (augS b) = _
  rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul, map_φO_aug, map_φO_aug M.C.T,
    M.hT0,
    Matrix.map_zero _ (map_zero _), Matrix.mul_zero, sub_zero]

/-- **The augmentation of the remaining complex is the old complex** (PROVED from `T₀ = 0`). -/
theorem aug_eq (i : ℕ) :
    (M.D.Ai i).map aug = (M.oldC.Ai i).map (algebraMap Lam OO) := by
  match i with
  | 0 => exact Matrix.ext fun j k => aug_φO (M.C.c0 (Sum.inl j) k)
  | 1 => exact Matrix.ext fun j k => aug_φO (M.C.X (Sum.inl j) (Sum.inr (Sum.inr k)))
  | 2 => exact Matrix.ext fun j k => congrArg (fun N => N j (Sum.inr (Sum.inr k))) M.d2_map_aug
  | _ + 3 => exact Matrix.ext fun j => j.elim0

/-- The sign evaluation of a matrix over `Λ[G]` mapped to `𝒪[G]` is a new-local Schur complement
(with the empty family: no poles). -/
theorem isNewLocalSchur_lam {r c : Type} [Fintype r] [Fintype c] [DecidableEq r] [DecidableEq c]
    (N : Matrix r c (MonoidAlgebra Lam (SignGroup b))) :
    IsNewLocalSchur (b := b) fun x => (N.map (φO b)).map (Determinant.signEval (sgnChar x)) := by
  refine ⟨Unit, Empty, inferInstance, inferInstance, inferInstance, inferInstance, fun _ => 0,
    fun _ => 0, fun _ => by norm_num, fun _ => 1, fun _ => 0, ?_, 0, ?_, r, c, inferInstance,
    inferInstance, N, 0, 0, 1, 1, ?_⟩
  · intro q; simp [Matrix.det_isEmpty]
  · ext i; exact i.1.elim
  · intro x
    dsimp only
    rw [map_φO_signEval]
    simp

/-- **The sign-evaluated surviving differential is the Schur complement of the new-local family**
(PROVED). -/
theorem poles2 : IsNewLocalSchur (b := b) fun x => M.D.d2.map (Determinant.signEval (sgnChar x)) := by
  refine ⟨M.Qn, M.ιn, inferInstance, inferInstance, inferInstance, inferInstance, M.A, M.dq, M.hd,
    M.v, M.w, M.hdet, M.Bsub, M.hB0, Fin M.D.m2, Fin M.D.m1 ⊕ Unit ⊕ Fin M.D.m2, inferInstance,
    inferInstance, M.C.P, M.C.Q.submatrix id M.eN.symm, M.C.T.submatrix M.eN.symm id, 1, 1,
    fun x => ?_⟩
  set f := (Determinant.signEval (O := OO) (sgnChar x)).toRingHom
  have hB : IsUnit (M.C.B.map (φO b)).det := M.isUnit_B
  have h1 : M.D.d2.map (Determinant.signEval (sgnChar x)) =
      (M.C.P.map (φO b) - M.C.Q.map (φO b) * (M.C.B.map (φO b))⁻¹ *
        M.C.T.map (φO b)).map f := rfl
  set Px := (M.C.P.map (Determinant.signEval (sgnChar x))).map (algebraMap Lam OO)
  set Qx := (M.C.Q.map (Determinant.signEval (sgnChar x))).map (algebraMap Lam OO)
  set Bx := (M.C.B.map (Determinant.signEval (sgnChar x))).map (algebraMap Lam OO)
  set Tx := (M.C.T.map (Determinant.signEval (sgnChar x))).map (algebraMap Lam OO)
  have hL : M.D.d2.map (Determinant.signEval (sgnChar x)) = Px - Qx * Bx⁻¹ * Tx := by
    rw [h1, Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul,
      map_inv_of_isUnit f _ hB]
    change (M.C.P.map (φO b)).map (Determinant.signEval (sgnChar x)) -
        (M.C.Q.map (φO b)).map (Determinant.signEval (sgnChar x)) *
          ((M.C.B.map (φO b)).map (Determinant.signEval (sgnChar x)))⁻¹ *
          (M.C.T.map (φO b)).map (Determinant.signEval (sgnChar x)) = _
    rw [map_φO_signEval, map_φO_signEval, map_φO_signEval, map_φO_signEval]
  have hR : (1 : Matrix (Fin M.C.m2) (Fin M.C.m2) Lam).map (algebraMap Lam OO) *
      (Px - (Qx.submatrix id M.eN.symm) * (Bx.submatrix M.eN.symm M.eN.symm)⁻¹ *
        (Tx.submatrix M.eN.symm id)) *
      (1 : Matrix (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) Lam).map
        (algebraMap Lam OO) = Px - Qx * Bx⁻¹ * Tx := by
    rw [Matrix.inv_submatrix_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_id_id, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, Matrix.mul_one]
  exact hL.trans hR.symm

/-- **The identification, derived from the new-local model** (PROVED). -/
def toIdentification : Identification b dK hK cE tK where
  D := M.D
  A0 := M.oldC.Ai
  s := M.s
  s_ne := M.s_ne
  central := M.central
  aug_eq := M.aug_eq
  poles0 := isNewLocalSchur_lam M.C.c0
  poles1 := isNewLocalSchur_lam M.C.X
  poles2 := M.poles2
  budget := M.budget

/-- The comparison of the remaining complex with the family Selmer complex is a quasi-isomorphism. -/
theorem comp_qis : QuasiIso (SelmerDuality.GHom.toCC (PreComplex.incl M.isUnit_B) ≫ M.ψ) := by
  have := PreComplex.incl_quasiIso M.isUnit_B
  have := M.qis
  infer_instance

/-- **The Selmer-phrased identification, derived from the new-local model** (PROVED): the
comparison is the inclusion of the remaining complex (a quasi-isomorphism) followed by the family
model. -/
def toSelmerIdentification : SelmerIdentification b dK hK cE tK where
  toIdentification := M.toIdentification
  sel := M.sel
  φ := SelmerDuality.GHom.toCC (PreComplex.incl M.isUnit_B) ≫ M.ψ
  qis := M.comp_qis

end NewLocalModel

/-- **RC0's `ClearingModel` from the new-local model and E1** (PROVED; E1 with the coordinate
parameter, `CoordParam.lean`). -/
theorem clearingModel_of_newLocal {ℓ : ℕ} (Dd : RCData ℓ)
    (h : ∃ dK hK cE tK : ℕ, ∀ Co Ce : ℤ, ∀ F : Family, Dd.FinalFamilyAt Co Ce F →
      ∃ (M : NewLocalModel F.b dK hK cE tK) (sd : ScalarData M.toIdentification.B)
        (κ ε η : MonoidAlgebra OO (SignGroup F.b)) (c : Addr F.b → FractionRing OO),
        CoordComputation M.toIdentification.B sd ε c M.D.RankOnePattern M.D.AcyclicPattern ∧
        ∀ (e : Addr F.b → ℕ) (g : Addr F.b → Lam), UTildeRep Dd F e g →
          CoordLink M.toIdentification.B κ η 0 e g c) :
    ClearingModel Dd := by
  obtain ⟨dK, hK, cE, tK, hF⟩ := h
  exact clearingModel_of_coord Dd ⟨dK, hK, cE, tK, fun Co Ce F hFam => by
    obtain ⟨M, sd, κ, ε, η, c, hcomp, hlink⟩ := hF Co Ce F hFam
    exact ⟨M.toSelmerIdentification, sd, κ, ε, η, c, hcomp, hlink⟩⟩

end ZInQ.Contrib.CloudB3RC53.ClearingComplex

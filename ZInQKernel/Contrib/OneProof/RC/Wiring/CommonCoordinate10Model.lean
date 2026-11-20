import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate10Retract
import ZInQKernel.Contrib.OneProof.RC.Limits.TriangularModel2

/-!
# The model of the relaxed complex as a full-condition pre-cancellation complex

Manuscript `diophantine_zq.tex`, the support triangle of Lemma `ex:arith-common-coordinate`
(tex 4157–4194: "Let `i : C_P → C_R` be the primitive-to-relaxed map") and the graded model of
the inclusion with quotient (tex 5398–5424: "the graded model of (5.6) is `C_old ⊕ ⊕_q Q_q` with
an upper triangular differential"; `B₀ = A = diag(A_q)`).

For a degreewise split inclusion `E : C_P ⊂ C_R` with quotient complex `Q`, a retract `R` of the
actual primitive complex `C_P` onto a block complex `D`, a retract `R_Q` of `Q` onto a model `Q'`
vanishing outside degrees one and two (e.g. the tame local model `twoSingCx` of (4.4)), and bases
`b1, b2` of `Q'¹, Q'²` indexed by `N`, this file extracts the matrices of the triangular model
`D ⊕ Q'` of `C_R` (lane RC31's two-piece `splitRetract₂`) into a `FullPreComplex`:

* `triIncl`: the inclusion `D → D ⊕ Q` of a triangular extension is a split inclusion with
  complement `0 ⊕ Q`; `triQBasis`: the bases of the complement; `triIncl_dQ`,
  `toMatrix_triIncl_dQ`: its quotient differential is `d_Q`.
* `relModel E R RQ b1 b2 := fullPreOfSplit D (triIncl …) …` (lane h17's pattern): `P = d¹_D`,
  `T = 0`, and the new block `B` is the matrix of the model quotient differential
  `d_{Q'} : Q'¹ → Q'²` in the bases `b1, b2` (`relModel_B`); its cancellation is `D`
  (`cancel_relModel`, `cancel_relModel_toFour`).
* `relRetract`: a normalized graded deformation retract of the actual `C_R` onto
  `relModel.toGCx` (`splitRetract₂` followed by the comparison `splitCoordHom`, a degreewise
  isomorphism, `retractOfModelEquiv`). With `R_Q` the identity retract of a finite quotient,
  this is lane RC31's one-piece `splitRetract` (`GRetract.triExt₂_refl_target`).
* The transport of the old part: the projection sends `i x` to `(p x, 0)`
  (`relRetract_p_i`), and the inclusion sends `(y, 0)` to `i (i_D y)` (`relRetract_i_inl`).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open Matrix Module ZInQ.Manuscript.RC.Limits ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.ClearingComplex

/-! ### The inclusion of a triangular extension is split -/

section TriIncl

variable {S : Type} [CommRing S] (X Q : GCx S) (δ : ∀ a b : ℤ, a + 1 = b → Q.X a →ₗ[S] X.X b)
  (hδ : ∀ a b c (hab : a + 1 = b) (hbc : b + 1 = c) (q : Q.X a),
    X.d b c hbc (δ a b hab q) + δ b c hbc (Q.d a b hab q) = 0)

/-- The inclusion `X → X ⊕ Q`, `x ↦ (x, 0)`, of a triangular extension is a chain map.
(tex 5398–5403) Kind: definition (PROVED identities). -/
def triInclHom : GHom X (triCx X Q δ hδ) where
  f a b h := by
    subst h
    exact LinearMap.inl S (X.X a) (Q.X a)
  comm := by
    intro i i₁ j j₁ hij h₁ h₂ hj x
    subst hij hj h₁
    change ((X.d i (i + 1) rfl x, 0) : X.X (i + 1) × Q.X (i + 1)) =
      (triCx X Q δ hδ).d i (i + 1) rfl ((x, 0) : X.X i × Q.X i)
    rw [triCx_d_apply, map_zero, add_zero, map_zero]

/-- **The inclusion of a triangular extension is a split inclusion** with complement `0 ⊕ Q`
(tex 5398–5403). Kind: definition (PROVED identities). -/
def triIncl : SplitInclusion X (triCx X Q δ hδ) where
  i := triInclHom X Q δ hδ
  inj _ := LinearMap.inl_injective
  Qc n := LinearMap.range (LinearMap.inr S (X.X n) (Q.X n))
  compl _ := LinearMap.isCompl_range_inl_inr

/-- `Q ≃ 0 ⊕ Q`. (tex 5398–5403) Kind: definition. -/
abbrev triQEquiv (n : ℤ) : Q.X n ≃ₗ[S] (triIncl X Q δ hδ).Qc n :=
  LinearEquiv.ofInjective (LinearMap.inr S (X.X n) (Q.X n)) LinearMap.inr_injective

/-- The basis of the complement `0 ⊕ Qⁿ` from a basis of `Qⁿ`. (tex 5398–5424)
Kind: definition. -/
def triQBasis {N : Type} (n : ℤ) (b : Basis N S (Q.X n)) : Basis N S ((triIncl X Q δ hδ).Qc n) :=
  b.map (triQEquiv X Q δ hδ n)

/-- The inclusion is `x ↦ (x, 0)`. (tex 5398–5403) Kind: PROVED (definitional). -/
theorem triIncl_i_apply (n : ℤ) (x : X.X n) :
    (triIncl X Q δ hδ).i.f n n rfl x = ((x, 0) : X.X n × Q.X n) :=
  rfl

/-- **The quotient differential of the triangular inclusion is `d_Q`** (tex 5398–5403).
Kind: PROVED. -/
theorem triIncl_dQ (a b : ℤ) (h : a + 1 = b) (y : Q.X a) :
    (triIncl X Q δ hδ).dQ a b h (triQEquiv X Q δ hδ a y) =
      triQEquiv X Q δ hδ b (Q.d a b h y) := by
  set E := triIncl X Q δ hδ
  have hd : (triCx X Q δ hδ).d a b h ((0, y) : X.X a × Q.X a) =
      E.i.f b b rfl (δ a b h y) + ((triQEquiv X Q δ hδ b (Q.d a b h y) : E.Qc b) :
        (triCx X Q δ hδ).X b) := by
    rw [triCx_d_apply, map_zero, zero_add]
    refine Prod.ext ?_ ?_
    · change δ a b h y = δ a b h y + 0
      rw [add_zero]
    · change Q.d a b h y = 0 + Q.d a b h y
      rw [zero_add]
  change E.coordQ b ((triCx X Q δ hδ).d a b h ((0, y) : X.X a × Q.X a)) = _
  rw [hd, map_add, E.coordQ_i, zero_add, E.coordQ_Q]

/-- **The matrix of the quotient differential in the transported bases is the matrix of `d_Q`**
(tex 5398–5424). Kind: PROVED. -/
theorem toMatrix_triIncl_dQ {N : Type} [Fintype N] [DecidableEq N] (b1 : Basis N S (Q.X 1))
    (b2 : Basis N S (Q.X 2)) :
    LinearMap.toMatrix (triQBasis X Q δ hδ 1 b1) (triQBasis X Q δ hδ 2 b2)
        ((triIncl X Q δ hδ).dQ 1 2 rfl) =
      LinearMap.toMatrix b1 b2 (Q.d 1 2 rfl) := by
  ext i j
  rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, triQBasis, triQBasis, Basis.map_apply,
    Basis.map_repr, LinearEquiv.trans_apply, triIncl_dQ, LinearEquiv.symm_apply_apply]

/-- Where `Qⁿ` vanishes, so does the complement `0 ⊕ Qⁿ`. (tex 5398–5424) Kind: PROVED. -/
theorem triIncl_Qc_eq_bot (n : ℤ) (hn : Subsingleton (Q.X n)) : (triIncl X Q δ hδ).Qc n = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨y, rfl⟩
  have hy : y = 0 := Subsingleton.elim _ _
  subst hy
  exact (Submodule.mem_bot S).2 (map_zero _)

end TriIncl

/-! ### The full-condition model of the relaxed complex -/

section Model

variable {F : Type} [Field F] {CP CR : GCx F} (E : SplitInclusion CP CR) {D : BlockComplex F}
  (R : GRetract CP D.toGCx) {Q' : GCx F} (RQ : GRetract E.quotientCx Q') {N : Type} [Fintype N]
  [DecidableEq N] (b1 : Basis N F (Q'.X 1)) (b2 : Basis N F (Q'.X 2))

/-- The triangular model `D ⊕ Q'` of the relaxed complex (lane RC31's `splitRetract₂` target).
(tex 5398–5403) Kind: definition. -/
abbrev triModel : GCx F :=
  triCx D.toGCx Q' (R.triδ₂ RQ E.offDiag) (R.triδ₂_sq RQ E.offDiag E.offDiag_sq)

/-- The split inclusion `D ⊂ D ⊕ Q'` of the triangular model. (tex 5398–5403)
Kind: definition. -/
abbrev triModelIncl : SplitInclusion D.toGCx (triModel E R RQ) :=
  triIncl D.toGCx Q' (R.triδ₂ RQ E.offDiag) (R.triδ₂_sq RQ E.offDiag E.offDiag_sq)

/-- The basis of the degree-one complement of the model inclusion. (tex 5398–5424)
Kind: definition. -/
abbrev relB1 : Basis N F ((triModelIncl E R RQ).Qc 1) :=
  triQBasis D.toGCx Q' (R.triδ₂ RQ E.offDiag) (R.triδ₂_sq RQ E.offDiag E.offDiag_sq) 1 b1

/-- The basis of the degree-two complement of the model inclusion. (tex 5398–5424)
Kind: definition. -/
abbrev relB2 : Basis N F ((triModelIncl E R RQ).Qc 2) :=
  triQBasis D.toGCx Q' (R.triδ₂ RQ E.offDiag) (R.triδ₂_sq RQ E.offDiag E.offDiag_sq) 2 b2

/-- **The model of the relaxed complex as a full-condition pre-cancellation complex**
(tex 5398–5424): the matrices of the triangular model `D ⊕ Q'` in the standard bases of `D` and
the bases `b1, b2` of `Q'¹, Q'²`, `fullPreOfSplit` of the inclusion `D ⊂ D ⊕ Q'`.
Kind: definition. -/
def relModel : FullPreComplex F :=
  fullPreOfSplit D (triModelIncl E R RQ) (relB1 E R RQ b1) (relB2 E R RQ b2)

/-- **The new block of the model is the matrix of the model quotient differential**
`d_{Q'} : Q'¹ → Q'²` in the bases `b1, b2` (tex 5420–5424: `B₀ = A = diag(A_q)`).
Kind: PROVED. -/
theorem relModel_B : (relModel E R RQ b1 b2).B = LinearMap.toMatrix b1 b2 (Q'.d 1 2 rfl) :=
  toMatrix_triIncl_dQ D.toGCx Q' _ _ b1 b2

/-- The model has the old block complex in its old positions: `m_i = m_i(D)`, `P = d¹_D`,
`T = 0`. (tex 5398–5424) Kind: PROVED (definitional). -/
theorem relModel_P : (relModel E R RQ b1 b2).P = D.d1 ∧ (relModel E R RQ b1 b2).T = 0 :=
  ⟨rfl, rfl⟩

/-- **Cancelling the new block of the model returns `D`** (tex 5424–5425).
Kind: PROVED. -/
theorem cancel_relModel (hB : IsUnit (relModel E R RQ b1 b2).B.det) :
    (relModel E R RQ b1 b2).cancel hB = D :=
  cancel_fullPreOfTriangular D N _ _ _
    (split_sq D (triModelIncl E R RQ) (relB1 E R RQ b1) (relB2 E R RQ b2)) hB

/-- The Schur differential of the cancelled model is `d¹_D` (`T = 0`). (tex 5424–5425)
Kind: PROVED. -/
theorem cancel_relModel_d1 (hB : IsUnit (relModel E R RQ b1 b2).B.det) :
    ((relModel E R RQ b1 b2).cancel hB).d1 = D.d1 := by
  show (relModel E R RQ b1 b2).P - (relModel E R RQ b1 b2).Q * (relModel E R RQ b1 b2).B⁻¹ *
    (relModel E R RQ b1 b2).T = D.d1
  rw [show (relModel E R RQ b1 b2).T = 0 from rfl, Matrix.mul_zero, sub_zero]
  rfl

/-- The cancelled model and `D` are the same four-term complex. (tex 5424–5425)
Kind: PROVED. -/
theorem cancel_relModel_toFour (hB : IsUnit (relModel E R RQ b1 b2).B.det) :
    ((relModel E R RQ b1 b2).cancel hB).toFour = D.toFour := by
  unfold BlockComplex.toFour
  congr 1
  exact cancel_relModel_d1 E R RQ b1 b2 hB

variable (hQ' : ∀ n, n ≠ 1 → n ≠ 2 → Subsingleton (Q'.X n))

include hQ' in
/-- The complements of the model inclusion vanish outside degrees one and two.
(tex 5398–5424) Kind: PROVED. -/
theorem triModelIncl_Qc (n : ℤ) (h1 : n ≠ 1) (h2 : n ≠ 2) : (triModelIncl E R RQ).Qc n = ⊥ :=
  triIncl_Qc_eq_bot _ _ _ _ n (hQ' n h1 h2)

/-- **The comparison of the model with the triangular model**, a degreewise isomorphism
(lane h17's `splitCoordL`, `splitCoordL_bijective`). (tex 5398–5424) Kind: definition. -/
def relCoordEquiv (n : ℤ) : (relModel E R RQ b1 b2).toGCx.X n ≃ₗ[F] (triModel E R RQ).X n :=
  LinearEquiv.ofBijective (splitCoordL D (triModelIncl E R RQ) _ _ n)
    (splitCoordL_bijective D (triModelIncl E R RQ) _ _
      (fun m h1 h2 => triModelIncl_Qc E R RQ hQ' m h1 h2) n)

/-- The comparison commutes with the differentials. (tex 5398–5424) Kind: PROVED. -/
theorem relCoordEquiv_comm (a b : ℤ) (h : a + 1 = b) (y : (relModel E R RQ b1 b2).toGCx.X a) :
    (triModel E R RQ).d a b h (relCoordEquiv E R RQ b1 b2 hQ' a y) =
      relCoordEquiv E R RQ b1 b2 hQ' b ((relModel E R RQ b1 b2).toGCx.d a b h y) := by
  subst h
  exact (splitCoordL_comm D (triModelIncl E R RQ) _ _
    (triModelIncl_Qc E R RQ hQ' 3 (by omega) (by omega)) a y).symm

/-- **The retract of the actual relaxed complex onto its full-condition model**
(tex 5398–5424, 4423–4437): `splitRetract₂ E R R_Q` followed by the inverse of the comparison.
Kind: definition (PROVED identities). -/
def relRetract : GRetract CR (relModel E R RQ b1 b2).toGCx :=
  retractOfModelEquiv (splitRetract₂ E R RQ) (relCoordEquiv E R RQ b1 b2 hQ')
    (relCoordEquiv_comm E R RQ b1 b2 hQ')

/-- The relaxed complex is homotopy equivalent to its full-condition model.
(tex 5398–5424) Kind: definition. -/
def relHomotopyEquiv :
    HomotopyEquiv (relModel E R RQ b1 b2).toGCx.toCC CR.toCC :=
  (relRetract E R RQ b1 b2 hQ').homotopyEquiv

/-! ### Transport of the old part -/

/-- The block equivalence sends `(x, 0)` to `i x`. (tex 5398–5403) Kind: PROVED. -/
theorem blockEquiv_symm_i (n : ℤ) (x : CP.X n) :
    (E.blockEquiv n).symm (E.i.f n n rfl x) = (x, 0) := by
  rw [LinearEquiv.symm_apply_eq, SplitInclusion.blockEquiv_apply, ZeroMemClass.coe_zero,
    add_zero]

/-- The projection of `splitRetract₂`: `p (blockEquiv⁻¹ x)` (degreewise).
(tex 5398–5403) Kind: PROVED (definitional). -/
theorem splitRetract₂_p_apply (n : ℤ) (x : CR.X n) :
    (splitRetract₂ E R RQ).p.f n n rfl x =
      (R.triExt₂ RQ E.offDiag E.offDiag_sq).p.f n n rfl ((E.blockEquiv n).symm x) :=
  rfl

/-- The inclusion of `splitRetract₂`: `blockEquiv (i' z)` (degreewise).
(tex 5398–5403) Kind: PROVED (definitional). -/
theorem splitRetract₂_i_apply (n : ℤ) (z : D.toGCx.X n × Q'.X n) :
    (splitRetract₂ E R RQ).i.f n n rfl z =
      E.blockEquiv n ((R.triExt₂ RQ E.offDiag E.offDiag_sq).i.f n n rfl z) :=
  rfl

/-- The projection of `splitRetract₂` sends `i x` to `(p x, 0)`. (tex 5398–5403)
Kind: PROVED. -/
theorem splitRetract₂_p_i (n : ℤ) (x : CP.X n) :
    (splitRetract₂ E R RQ).p.f n n rfl (E.i.f n n rfl x) =
      ((R.p.f n n rfl x, 0) : D.toGCx.X n × Q'.X n) := by
  rw [splitRetract₂_p_apply, blockEquiv_symm_i]
  refine (GRetract.triExt₂_p_apply R RQ E.offDiag E.offDiag_sq n x 0).trans ?_
  refine Prod.ext ?_ ?_
  · have h1 : (RQ.h n (n - 1) (by omega) 0 : E.Qc (n - 1)) = 0 := map_zero _
    have h2 : E.offDiag (n - 1) n (by omega) (RQ.h n (n - 1) (by omega) 0) = 0 :=
      (congrArg (E.offDiag (n - 1) n (by omega)) h1).trans (map_zero _)
    change R.p.f n n rfl x - R.p.f n n rfl (E.offDiag (n - 1) n (by omega)
      (RQ.h n (n - 1) (by omega) 0)) = R.p.f n n rfl x
    rw [h2, map_zero, sub_zero]
  · exact map_zero _

/-- The inclusion of `splitRetract₂` sends `(y, 0)` to `i (i_D y)`. (tex 5398–5403)
Kind: PROVED. -/
theorem splitRetract₂_i_inl (n : ℤ) (y : D.toGCx.X n) :
    (splitRetract₂ E R RQ).i.f n n rfl ((y, 0) : D.toGCx.X n × Q'.X n) =
      E.i.f n n rfl (R.i.f n n rfl y) := by
  rw [splitRetract₂_i_apply]
  have h : (R.triExt₂ RQ E.offDiag E.offDiag_sq).i.f n n rfl
      ((y, 0) : D.toGCx.X n × Q'.X n) = ((R.i.f n n rfl y, 0) : CP.X n × E.quotientCx.X n) := by
    refine (GRetract.triExt₂_i_apply R RQ E.offDiag E.offDiag_sq n y 0).trans ?_
    refine Prod.ext ?_ ?_
    · have h1 : (RQ.i.f n n rfl 0 : E.Qc n) = 0 := map_zero _
      have h2 : E.offDiag n (n + 1) rfl (RQ.i.f n n rfl 0) = 0 :=
        (congrArg (E.offDiag n (n + 1) rfl) h1).trans (map_zero _)
      change R.i.f n n rfl y - R.h (n + 1) n rfl (E.offDiag n (n + 1) rfl
        (RQ.i.f n n rfl 0)) = R.i.f n n rfl y
      rw [h2, map_zero, sub_zero]
    · exact map_zero _
  rw [h]
  change E.blockEquiv n ((R.i.f n n rfl y, (0 : E.Qc n)) : CP.X n × E.Qc n) = _
  rw [SplitInclusion.blockEquiv_apply, ZeroMemClass.coe_zero, add_zero]

/-! ### The old part in model coordinates -/

/-- The comparison sends `(y, 0)` in degree one to `(y, 0)`. (tex 5398–5424) Kind: PROVED. -/
theorem relCoordEquiv_one_inl (y : Fin D.m0 ⊕ Unit ⊕ Fin D.m1 → F) :
    relCoordEquiv E R RQ b1 b2 hQ' 1 (Sum.elim y (0 : N → F)) =
      ((y, 0) : D.toGCx.X 1 × Q'.X 1) := by
  change (triModelIncl E R RQ).i.f 1 1 rfl y +
    ((relB1 E R RQ b1).equivFun.symm (0 : N → F) : (triModel E R RQ).X 1) = _
  simp only [map_zero, ZeroMemClass.coe_zero, add_zero]
  rfl

/-- The comparison sends `(y, 0)` in degree two to `(y, 0)`. (tex 5398–5424) Kind: PROVED. -/
theorem relCoordEquiv_two_inl (y : Fin D.m1 ⊕ Unit ⊕ Fin D.m2 → F) :
    relCoordEquiv E R RQ b1 b2 hQ' 2 (Sum.elim y (0 : N → F)) =
      ((y, 0) : D.toGCx.X 2 × Q'.X 2) := by
  change (triModelIncl E R RQ).i.f 2 2 rfl y +
    ((relB2 E R RQ b2).equivFun.symm (0 : N → F) : (triModel E R RQ).X 2) = _
  simp only [map_zero, ZeroMemClass.coe_zero, add_zero]
  rfl

/-- **The model of an old cycle**: the projection of the relaxed retract sends `i x` to
`(p x, 0)` in the coordinates of the model (tex 4166–4170, 5398–5424). Kind: PROVED. -/
theorem relRetract_p_i_one (x : CP.X 1) :
    (relRetract E R RQ b1 b2 hQ').p.f 1 1 rfl (E.i.f 1 1 rfl x) =
      (Sum.elim (R.p.f 1 1 rfl x) (0 : N → F) : (relModel E R RQ b1 b2).toGCx.X 1) := by
  rw [relRetract, retractOfModelEquiv_p, splitRetract₂_p_i]
  refine (LinearEquiv.symm_apply_eq _).2 ?_
  exact (relCoordEquiv_one_inl E R RQ b1 b2 hQ' _).symm

/-- **The model of an old functional**: the inclusion of the relaxed retract sends `(y, 0)` in
degree two to `i (i_D y)` (tex 4166–4172, 5398–5424). Kind: PROVED. -/
theorem relRetract_i_two_inl (y : Fin D.m1 ⊕ Unit ⊕ Fin D.m2 → F) :
    (relRetract E R RQ b1 b2 hQ').i.f 2 2 rfl (Sum.elim y (0 : N → F)) =
      E.i.f 2 2 rfl (R.i.f 2 2 rfl y) := by
  change (splitRetract₂ E R RQ).i.f 2 2 rfl
    (relCoordEquiv E R RQ b1 b2 hQ' 2 (Sum.elim y 0)) = _
  exact (congrArg ((splitRetract₂ E R RQ).i.f 2 2 rfl)
    (relCoordEquiv_two_inl E R RQ b1 b2 hQ' y)).trans (splitRetract₂_i_inl E R RQ 2 y)

/-- A standard basis vector of `D² ⊕ N` on the old part. (tex 5398–5424) Kind: PROVED. -/
theorem single_inl_eq {α β : Type} [DecidableEq α] [DecidableEq β] (j : α) :
    (Pi.single (Sum.inl j) (1 : F) : α ⊕ β → F) = Sum.elim (Pi.single j 1) 0 := by
  funext k
  rcases k with k | k
  · simp [Pi.single_apply]
  · simp

/-- **The model functional on the old part** (tex 4166–4172): the coordinate vector of `λ ∘ i_R`
restricted to `D²` is the coordinate vector of `(λ ∘ i) ∘ i_D`. Kind: PROVED. -/
theorem funVec_relRetract_inl (lam : CR.X 2 →ₗ[F] F) :
    funVec (ι := (Fin D.m1 ⊕ Unit ⊕ Fin D.m2) ⊕ N)
        (lam ∘ₗ (relRetract E R RQ b1 b2 hQ').i.f 2 2 rfl) ∘ Sum.inl =
      funVec (ι := Fin D.m1 ⊕ Unit ⊕ Fin D.m2) ((lam ∘ₗ E.i.f 2 2 rfl) ∘ₗ R.i.f 2 2 rfl) := by
  funext j
  change lam ((relRetract E R RQ b1 b2 hQ').i.f 2 2 rfl
      (Pi.single (Sum.inl j) 1 : (Fin D.m1 ⊕ Unit ⊕ Fin D.m2) ⊕ N → F)) =
    lam (E.i.f 2 2 rfl (R.i.f 2 2 rfl (Pi.single j 1 : Fin D.m1 ⊕ Unit ⊕ Fin D.m2 → F)))
  rw [single_inl_eq]
  exact congrArg lam (relRetract_i_two_inl E R RQ b1 b2 hQ' _)

end Model

end ZInQ.Manuscript.RC.Wiring

import ZInQKernel.Contrib.OneProof.RC.Local.TameFreeModel
import ZInQKernel.Contrib.OneProof.RC.Limits.FieldModel
import ZInQKernel.Contrib.OneProof.RC.Limits.TriangularModel

/-!
# Lane RC31, round 5: the two-place block of the support triangle in model coordinates

Manuscript `diophantine_zq.tex`, tex 4176–4184 ((4.7): the quotient determinants
`δ_q = det(zFr_q − q) · det(z⁻¹Fr_q − q)` at the two conjugate places of an unused split prime),
tex 5398–5424 (the triangular model of the relaxation), tex 3470–3480 ((4.4)).

For a split inclusion `E : D ⊂ C_R` of the primitive block complex into a relaxed model
(`SplitInclusion`, `fullPreOfSplit`), if the quotient differential `d_Q : Q¹ → Q²` is, in
coordinates `Q¹ ≃ A^(2 ⊕ 2)`, `Q² ≃ A^(2 ⊕ 2)` of the two places, the differential of the two
singular blocks `[A² --zF−q--> A²] ⊕ [A² --z⁻¹F−q--> A²]` (`twoSingD12`), then the new singular
block of the full-condition pre-cancellation complex is `twoPlaceBlock F q z z⁻¹`:
`splitB_eq_twoPlaceBlock`, `fullPreOfSplit_B_eq_twoPlaceBlock`, and the exact form of the
hypothesis `hBe` of the torsion-level step `KmStep` (`fullPreOfSplit_hBe`).

The hypothesis on `d_Q` is what the two-piece triangular model (`splitRetract₂`, with quotient
model the two singular blocks of the tame models at `w`, `w̄`: `twoSingCx`) provides.

Kinds: PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Local

open Module
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Manuscript.RC.Limits
open ZInQ.Contrib.CloudB3RC53.ClearingComplex
open ZInQ.Contrib.CloudB3RC53.CommonCoordinate (twoPlaceBlock)

variable {S : Type} [CommRing S]

/-- **The new singular block is the two-place block** (tex 4176–4184, 5420–5424): if the quotient
differential of a split inclusion is the differential of the two singular blocks in coordinates
`e₁`, `e₂` of the two places, its matrix in the bases `e₁⁻¹`, `e₂⁻¹` is `twoPlaceBlock F q z z⁻¹`.
Kind: PROVED. -/
theorem splitB_eq_twoPlaceBlock (D : BlockComplex S) {CR : GCx S}
    (E : SplitInclusion D.toGCx CR) (F : Matrix (Fin 2) (Fin 2) S) (q : ℕ) (z zi : S)
    (e1 : E.Qc 1 ≃ₗ[S] (Fin 2 ⊕ Fin 2 → S)) (e2 : E.Qc 2 ≃ₗ[S] (Fin 2 ⊕ Fin 2 → S))
    (he : ∀ x, e2 (E.dQ 1 2 rfl x) = twoSingD12 F q z zi (e1 x)) :
    splitB D E (Basis.ofEquivFun e1) (Basis.ofEquivFun e2) = twoPlaceBlock F (q : S) z zi := by
  rw [← twoSing_matrix F q z zi]
  ext i j
  rw [splitB, LinearMap.toMatrix_apply, Basis.ofEquivFun_repr_apply, Basis.coe_ofEquivFun, he,
    LinearEquiv.apply_symm_apply, LinearMap.toMatrix'_apply]

/-- **The full-condition pre-cancellation complex has the two-place block** (tex 4176–4184,
5398–5424). Kind: PROVED. -/
theorem fullPreOfSplit_B_eq_twoPlaceBlock (D : BlockComplex S) {CR : GCx S}
    (E : SplitInclusion D.toGCx CR) (F : Matrix (Fin 2) (Fin 2) S) (q : ℕ) (z zi : S)
    (e1 : E.Qc 1 ≃ₗ[S] (Fin 2 ⊕ Fin 2 → S)) (e2 : E.Qc 2 ≃ₗ[S] (Fin 2 ⊕ Fin 2 → S))
    (he : ∀ x, e2 (E.dQ 1 2 rfl x) = twoSingD12 F q z zi (e1 x)) :
    (fullPreOfSplit D E (Basis.ofEquivFun e1) (Basis.ofEquivFun e2)).B =
      twoPlaceBlock F (q : S) z zi :=
  splitB_eq_twoPlaceBlock D E F q z zi e1 e2 he

/-- **The block hypothesis of the torsion-level step** (tex 4176–4184; the hypothesis `hBe` of
`KmStep`): `∃ e, B = (twoPlaceBlock F q z z⁻¹).submatrix e e`, with `e` the identity. Kind:
PROVED. -/
theorem fullPreOfSplit_hBe (D : BlockComplex S) {CR : GCx S}
    (E : SplitInclusion D.toGCx CR) (F : Matrix (Fin 2) (Fin 2) S) (q : ℕ) (z zi : S)
    (e1 : E.Qc 1 ≃ₗ[S] (Fin 2 ⊕ Fin 2 → S)) (e2 : E.Qc 2 ≃ₗ[S] (Fin 2 ⊕ Fin 2 → S))
    (he : ∀ x, e2 (E.dQ 1 2 rfl x) = twoSingD12 F q z zi (e1 x)) :
    ∃ e : (fullPreOfSplit D E (Basis.ofEquivFun e1) (Basis.ofEquivFun e2)).N ≃ Fin 2 ⊕ Fin 2,
      (fullPreOfSplit D E (Basis.ofEquivFun e1) (Basis.ofEquivFun e2)).B =
        (twoPlaceBlock F (q : S) z zi).submatrix e e :=
  ⟨Equiv.refl _, by
    rw [fullPreOfSplit_B_eq_twoPlaceBlock D E F q z zi e1 e2 he]
    rfl⟩

/-! ### The triangular model as a split inclusion -/

section TriSplit

variable {Y Q : GCx S} (δ : ∀ a b : ℤ, a + 1 = b → Q.X a →ₗ[S] Y.X b)
  (hδ : ∀ a b c (hab : a + 1 = b) (hbc : b + 1 = c) (q : Q.X a),
    Y.d b c hbc (δ a b hab q) + δ b c hbc (Q.d a b hab q) = 0)

/-- **The inclusion of the first block of a triangular complex** `y ↦ (y, 0)` (tex 5398–5424).
Kind: definition (PROVED chain property). -/
def triInl : GHom Y (triCx Y Q δ hδ) where
  f i j h := by
    subst h
    exact LinearMap.inl S (Y.X i) (Q.X i)
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj
    change ((Y.d i i₁ h₁ x, (0 : Q.X i₁)) : Y.X i₁ × Q.X i₁) =
      (triCx Y Q δ hδ).d i i₁ h₂ ((x, 0) : Y.X i × Q.X i)
    rw [triCx_d_apply, map_zero, map_zero, add_zero]

/-- **The triangular complex as a split inclusion** of its first block, with complement the
second block (tex 5398–5424). Kind: definition. -/
def triSplitInclusion : SplitInclusion Y (triCx Y Q δ hδ) where
  i := triInl δ hδ
  inj _ _ _ h := congrArg Prod.fst h
  Qc n := LinearMap.range (LinearMap.inr S (Y.X n) (Q.X n))
  compl _ := LinearMap.isCompl_range_inl_inr

/-- The complement of the triangular split is the second block. Kind: definition. -/
def triQEquiv (n : ℤ) : (triSplitInclusion δ hδ).Qc n ≃ₗ[S] Q.X n :=
  (LinearEquiv.ofInjective (LinearMap.inr S (Y.X n) (Q.X n)) LinearMap.inr_injective).symm

/-- The inverse of `triQEquiv` is `q ↦ (0, q)`. Kind: PROVED (definitional). -/
theorem triQEquiv_symm_apply (n : ℤ) (q : Q.X n) :
    (((triQEquiv δ hδ n).symm q : (triSplitInclusion δ hδ).Qc n) : (triCx Y Q δ hδ).X n) =
      (((0 : Y.X n), q) : Y.X n × Q.X n) :=
  rfl

/-- **The quotient differential of the triangular split is the second block's differential**
(tex 5398–5424). Kind: PROVED. -/
theorem triSplit_dQ (q : Q.X 1) :
    triQEquiv δ hδ 2 ((triSplitInclusion δ hδ).dQ 1 2 rfl ((triQEquiv δ hδ 1).symm q)) =
      Q.d 1 2 rfl q := by
  have hdec : (triCx Y Q δ hδ).d 1 2 rfl (((0 : Y.X 1), q) : Y.X 1 × Q.X 1) =
      (triSplitInclusion δ hδ).i.f 2 2 rfl (δ 1 2 rfl q) +
        (((triQEquiv δ hδ 2).symm (Q.d 1 2 rfl q) : (triSplitInclusion δ hδ).Qc 2) :
          (triCx Y Q δ hδ).X 2) := by
    rw [triCx_d_apply, map_zero, zero_add, triQEquiv_symm_apply]
    exact Prod.ext (add_zero _).symm (zero_add _).symm
  have h : (triSplitInclusion δ hδ).dQ 1 2 rfl ((triQEquiv δ hδ 1).symm q) =
      (triQEquiv δ hδ 2).symm (Q.d 1 2 rfl q) := by
    change (triSplitInclusion δ hδ).coordQ 2
      ((triCx Y Q δ hδ).d 1 2 rfl (((0 : Y.X 1), q) : Y.X 1 × Q.X 1)) = _
    rw [hdec, map_add, SplitInclusion.coordQ_i, SplitInclusion.coordQ_Q, zero_add]
  rw [h, LinearEquiv.apply_symm_apply]

end TriSplit

/-! ### The two-place block of a triangular model with the two singular blocks -/

section TwoPiece

variable (F : Matrix (Fin 2) (Fin 2) S) (q : ℕ) (z zi : S) (D : BlockComplex S)
  (δ : ∀ a b : ℤ, a + 1 = b → (twoSingCx F q z zi).X a →ₗ[S] D.toGCx.X b)
  (hδ : ∀ a b c (hab : a + 1 = b) (hbc : b + 1 = c) (x : (twoSingCx F q z zi).X a),
    D.toGCx.d b c hbc (δ a b hab x) + δ b c hbc ((twoSingCx F q z zi).d a b hab x) = 0)

/-- The coordinates of the two places on the complement of the triangular split, degree one.
Kind: definition. -/
def twoPieceCoord1 : (triSplitInclusion δ hδ).Qc 1 ≃ₗ[S] (Fin 2 ⊕ Fin 2 → S) :=
  (triQEquiv δ hδ 1).trans (twoPlaceCoord (A := S)).symm

/-- The coordinates of the two places on the complement of the triangular split, degree two.
Kind: definition. -/
def twoPieceCoord2 : (triSplitInclusion δ hδ).Qc 2 ≃ₗ[S] (Fin 2 ⊕ Fin 2 → S) :=
  (triQEquiv δ hδ 2).trans (twoPlaceCoord (A := S)).symm

/-- **The two-place block of the triangular model** (tex 4176–4184, 5398–5424): for a triangular
model `D ⊕_δ (two singular blocks)` of the relaxed complex over the primitive block complex `D`,
the full-condition pre-cancellation complex built from the triangular split has new singular
block `twoPlaceBlock F q z z⁻¹` — the block hypothesis `hBe` of `KmStep`. Kind: PROVED. -/
theorem twoPiece_hBe :
    ∃ e : (fullPreOfSplit D (triSplitInclusion δ hδ)
        (Basis.ofEquivFun (twoPieceCoord1 F q z zi D δ hδ))
        (Basis.ofEquivFun (twoPieceCoord2 F q z zi D δ hδ))).N ≃ Fin 2 ⊕ Fin 2,
      (fullPreOfSplit D (triSplitInclusion δ hδ)
        (Basis.ofEquivFun (twoPieceCoord1 F q z zi D δ hδ))
        (Basis.ofEquivFun (twoPieceCoord2 F q z zi D δ hδ))).B =
        (twoPlaceBlock F (q : S) z zi).submatrix e e := by
  refine fullPreOfSplit_hBe D (triSplitInclusion δ hδ) F q z zi _ _ (fun x => ?_)
  obtain ⟨y, rfl⟩ := (triQEquiv δ hδ 1).symm.surjective x
  change (twoPlaceCoord (A := S)).symm (triQEquiv δ hδ 2
      ((triSplitInclusion δ hδ).dQ 1 2 rfl ((triQEquiv δ hδ 1).symm y))) =
    twoSingD12 F q z zi ((twoPlaceCoord (A := S)).symm (triQEquiv δ hδ 1
      ((triQEquiv δ hδ 1).symm y)))
  rw [triSplit_dQ, LinearEquiv.apply_symm_apply]
  have e2 := (twoSingD12_eq F q z zi ((twoPlaceCoord (A := S)).symm y)).trans
    (congrArg ((twoSingCx F q z zi).d 1 2 rfl) ((twoPlaceCoord (A := S)).apply_symm_apply y))
  exact (congrArg (twoPlaceCoord (A := S)).symm e2.symm).trans
    ((twoPlaceCoord (A := S)).symm_apply_apply _)

end TwoPiece

end ZInQ.Manuscript.RC.Local

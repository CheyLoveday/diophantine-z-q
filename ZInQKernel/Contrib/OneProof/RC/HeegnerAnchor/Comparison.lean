import ZInQKernel.Contrib.OneProof.RC.PreparedParam.Parametrization
import ZInQKernel.Contrib.CloudB3E2Norm.H20Anchor

/-! At a CM point, evaluating the fixed morphism over its ring class field
commutes with the anchor's chosen complex embedding (tex 2915–2917).
The field embedding and base change arguments are on-the-spot (c). -/

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField WeierstrassCurve
  TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
  ZInQ.Contrib.CloudB3E2.NormCochain ZInQ.Contrib.CloudB3RC53.CST
  ZInQ.Manuscript.RC.PreparedParam ZInQ.Manuscript.RC.PrintsArith

namespace ZInQ.Manuscript.RC.HeegnerAnchor

/-- An embedding of an algebraic field into `ℂ` factors through the given
embedding of `ℚ̄`: every minimal polynomial splits in the latter's image. -/
private theorem factor_embedding {H : Type} [Field H] [Algebra ℚ H] [Algebra.IsAlgebraic ℚ H]
    (ι : Qbar →ₐ[ℚ] ℂ) (j : H →ₐ[ℚ] ℂ) :
    ∃ e : H →ₐ[ℚ] Qbar, ι.comp e = j := by
  have hs (a : H) : ((minpoly ℚ a).map (algebraMap ℚ ι.fieldRange)).Splits :=
    Polynomial.Splits.of_algHom (IsAlgClosed.splits _) ι.rangeRestrict
  let F := IntermediateField.algHomEquivAlgHomOfSplits ℂ ι.fieldRange hs
  let b := F.symm j
  refine ⟨ι.equivFieldRange.symm.toAlgHom.comp b, ?_⟩
  apply AlgHom.ext
  intro a
  change ((ι.equivFieldRange (ι.equivFieldRange.symm (b a)) : ι.fieldRange) : ℂ) = j a
  rw [AlgEquiv.apply_symm_apply]
  exact DFunLike.congr_fun (F.apply_symm_apply j) a

private theorem fieldPoint_map_map {X : Scheme.{0}} {p : X ⟶ Spec (.of ℚ)}
    {F G L : Type} [Field F] [Field G] [Field L] [Algebra ℚ F] [Algebra ℚ G] [Algebra ℚ L]
    (e : F →ₐ[ℚ] G) (j : G →ₐ[ℚ] L) (x : FieldPoint p F) :
    (x.map e).map j = x.map (j.comp e) := by
  apply Subtype.ext
  simp only [FieldPoint.map, ← Category.assoc, ← Spec.map_comp]
  rfl

open Classical in
/-- The fixed morphism sends a descended CM point to the prescribed
analytic value under the chosen embedding, including at the origin. -/
theorem cmPointValue {E : WeierstrassCurve ℚ} [E.IsElliptic] [NeZero (newformLevel E)]
    {X : X0Model (newformLevel E)} (hCM : CMFieldOfDefinition X) (p : CSTParam E)
    (π : X.X ⟶ Proj E.toProjective.grading) (hπQ : π ≫ projectiveOverQ E = X.overQ)
    (hπ : ∀ τ : UpperHalfPlane,
      projectiveValue ((X.complexPoint τ).comp π hπQ).val = phiAn E p.f p.Lat p.κ τ)
    (ι : Qbar →ₐ[ℚ] ℂ) {K : Type} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (hKC : IsTotallyComplex K)
    (O : NumberFieldOrder K) {Δ A B C : ℤ} (hO : O.discr = Δ) (hΔ : Δ < 0)
    (hcop : IsCoprime Δ (newformLevel E : ℤ))
    (hform : IsHeegnerForm (newformLevel E) Δ A B C) :
    ∃ (e : ringClassField O →ₐ[ℚ] Qbar) (x : FieldPoint X.overQ e.fieldRange),
      x.map (ι.comp e.fieldRange.val) = X.complexPoint (cmPoint A B Δ) ∧
      Affine.Point.map (W' := E) ι
        (Affine.Point.map (W' := E) e.fieldRange.val (projectiveValue (x.comp π hπQ).val)) =
          phiAn E p.f p.Lat p.κ (cmPoint A B Δ) := by
  obtain ⟨j, x, hx⟩ := hCM K hK hKC O Δ A B C hO hΔ hcop hform
  obtain ⟨e, he⟩ := factor_embedding ι j
  let j' := ι.comp e.fieldRange.val
  let e' := e.equivFieldRange.toAlgHom
  let x' := x.map e'
  have hx' : x'.map j' = X.complexPoint (cmPoint A B Δ) := by
    change (x.map e').map j' = _
    rw [fieldPoint_map_map]
    have he' : j'.comp e' = j := he
    rwa [he']
  refine ⟨e, x', hx', ?_⟩
  rw [Affine.Point.map_map]
  calc
    _ = projectiveValue (Spec.map (CommRingCat.ofHom j'.toRingHom) ≫ (x'.comp π hπQ).val) :=
      projectiveValue_map j' _
    _ = projectiveValue ((x'.map j').comp π hπQ).val := by
      simp only [FieldPoint.comp, FieldPoint.map, Category.assoc]
    _ = _ := by rw [hx']; exact hπ _

#print axioms factor_embedding
#print axioms fieldPoint_map_map
#print axioms cmPointValue

end ZInQ.Manuscript.RC.HeegnerAnchor

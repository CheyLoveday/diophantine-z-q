import ZInQKernel.Contrib.OneProof.RC.HeegnerAnchor.Conductors
import ZInQKernel.Contrib.OneProof.RC.ParamJoin.AtScale
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.GenusTheoryReduction
import ZInQKernel.Contrib.OneProof.RC.HeegnerAnchor.Comparison

/-!
# The Heegner anchor from the fixed-scale morphism

Tex 2915–2917: the embedded CM point is read at its Heegner root, and
the rational morphism gives its elliptic image over the same field.
Factoring through the specified embedding and packing the anchor are
on-the-spot (c).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField WeierstrassCurve
  TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
  ZInQ.Contrib.CloudB3E2.NormCochain
  ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd
  ZInQ.Manuscript.RC.PreparedParam ZInQ.Manuscript.RC.PrintsArith ZInQ.Manuscript.RC.Wiring

namespace ZInQ.Manuscript.RC.HeegnerAnchor

open Classical in
/-- The source chart and elliptic image for one order of discriminant `Δ`.
Keeping the chart abstract here avoids unfolding its construction when
elaborating the comparison on the actual modular curve. -/
private def ConductorComparison {E : WeierstrassCurve ℚ} [E.IsElliptic]
    [NeZero (newformLevel E)] {K : Type} [Field K] [NumberField K]
    (p : CSTParam E) (ι : Qbar →ₐ[ℚ] ℂ) (X : X0Model (newformLevel E))
    (π : X.X ⟶ Proj E.toProjective.grading) (hπQ : π ≫ projectiveOverQ E = X.overQ)
    (O : NumberFieldOrder K) (Δ : ℤ) : Prop :=
  ∃ (B C : ℤ) (e : ringClassField O →ₐ[ℚ] Qbar) (x : FieldPoint X.overQ e.fieldRange),
    IsHeegnerForm (newformLevel E) Δ (newformLevel E : ℤ) B C ∧
    x.map (ι.comp e.fieldRange.val) = X.complexPoint (cmPoint (newformLevel E : ℤ) B Δ) ∧
    Affine.Point.map (W' := E) ι
      (Affine.Point.map (W' := E) e.fieldRange.val (projectiveValue (x.comp π hπQ).val)) =
        phiAn E p.f p.Lat p.κ (cmPoint (newformLevel E : ℤ) B Δ)

set_option maxHeartbeats 800000 in
open Classical in
/-- One rational morphism works for every admissible conductor on the
constructed modular curve. The source point, its chart, and its evaluated
image all use the same embedding of the ring class field. -/
theorem cmPointsAtScale {ℓ : ℕ} [(Ecurve ℓ).IsElliptic] [NeZero (newformLevel (Ecurve ℓ))]
    {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
    (p : CSTParam (Ecurve ℓ)) (ι : Qbar →ₐ[ℚ] ℂ)
    (hK : Module.finrank ℚ K = 2)
    (hsplit : ∀ q : ℕ, q.Prime → q ∣ 2 * newformLevel (Ecurve ℓ) → SplitsIn K q)
    (hr : ∃ c : ℚ, (c : ℂ) = p.κ)
    (hCM : CMFieldOfDefinition (X0Branch.model (newformLevel (Ecurve ℓ)))) :
    let X := X0Branch.model (newformLevel (Ecurve ℓ))
    ∃ (π : X.X ⟶ Proj (Ecurve ℓ).toProjective.grading)
      (hπQ : π ≫ projectiveOverQ (Ecurve ℓ) = X.overQ),
      IsDominant π ∧ ∀ (d : ℕ) (hd : 0 < d),
        Nat.Coprime d (newformLevel (Ecurve ℓ) * (discr K).natAbs) →
        ConductorComparison p ι X π hπQ
          (@conductorOrder K _ _ d ⟨hd.ne'⟩) (discr K * (d : ℤ) ^ 2) := by
  obtain ⟨π, hπQ, hdom, hπ⟩ :=
    ParamJoin.algebraicParametrizationAtScale (ℓ := ℓ) p.f p.hf p.hLat p.hκ hr
  refine ⟨π, hπQ, hdom, fun d hd hcop => ?_⟩
  let _ : NeZero d := ⟨hd.ne'⟩
  obtain ⟨hcop', B, C, hform⟩ :=
    conductorForm (N := newformLevel (Ecurve ℓ)) hK (NeZero.pos _) hsplit hcop
  have hΔ : discr K * (d : ℤ) ^ 2 < 0 :=
    mul_neg_of_neg_of_pos (discr_neg_of_totallyComplex hK) (pow_pos (by exact_mod_cast hd) 2)
  obtain ⟨e, x, hx, hy⟩ := cmPointValue hCM p π hπQ hπ ι hK inferInstance
    (conductorOrder K d) (conductorOrder_discr hK d) hΔ hcop' hform
  exact ⟨B, C, e, x, hform, hx, hy⟩

set_option maxHeartbeats 800000 in
open Classical in
/-- The CM evaluation supplies the fields and points of the anchor.
The caller can fill the two Galois slots of `HeegnerPointData` without
changing this assertion about the points. -/
theorem genuineHeegnerAnchor {ℓ : ℕ} [(Ecurve ℓ).IsElliptic] [NeZero (newformLevel (Ecurve ℓ))]
    {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
    (p : CSTParam (Ecurve ℓ)) (ι : Qbar →ₐ[ℚ] ℂ)
    (hK : Module.finrank ℚ K = 2)
    (hsplit : ∀ q : ℕ, q.Prime → q ∣ 2 * newformLevel (Ecurve ℓ) → SplitsIn K q)
    (hr : ∃ c : ℚ, (c : ℂ) = p.κ)
    (hCM : CMFieldOfDefinition (X0Branch.model (newformLevel (Ecurve ℓ)))) :
    ∃ (H : ℕ → IntermediateField ℚ Qbar) (y : ℕ → ((Ecurve ℓ).baseChange Qbar).toAffine.Point),
      ∀ (relGal : ℕ → ℕ → Finset GalQ) (frob : ℕ → ℕ → GalQ),
        GenuineHeegnerAnchor (Ecurve ℓ) K p ι
          ⟨discr K, newformLevel (Ecurve ℓ), H, y, relGal, frob⟩ := by
  obtain ⟨π, hπQ, -, hpts⟩ := cmPointsAtScale p ι hK hsplit hr hCM
  have hy (d : ℕ) (hd : 0 < d)
      (hcop : Nat.Coprime d (newformLevel (Ecurve ℓ) * (discr K).natAbs)) :
      ∃ (Hd : IntermediateField ℚ Qbar) (Y : ((Ecurve ℓ).baseChange Hd).toAffine.Point),
        ∃ A B C : ℤ, IsHeegnerForm (newformLevel (Ecurve ℓ)) (discr K * (d : ℤ) ^ 2) A B C ∧
          Affine.Point.map (W' := Ecurve ℓ) ι (Affine.Point.map (W' := Ecurve ℓ) Hd.val Y) =
            phiAn (Ecurve ℓ) p.f p.Lat p.κ (cmPoint A B (discr K * (d : ℤ) ^ 2)) := by
    have h := hpts d hd hcop
    unfold ConductorComparison at h
    obtain ⟨B, C, e, x, hform, -, hvalue⟩ := h
    exact ⟨e.fieldRange, projectiveValue (x.comp π hπQ).val, _, B, C, hform, hvalue⟩
  let H (d : ℕ) : IntermediateField ℚ Qbar :=
    if h : 0 < d ∧ Nat.Coprime d (newformLevel (Ecurve ℓ) * (discr K).natAbs)
      then (hy d h.1 h.2).choose else ⊥
  let y (d : ℕ) : ((Ecurve ℓ).baseChange Qbar).toAffine.Point :=
    if h : 0 < d ∧ Nat.Coprime d (newformLevel (Ecurve ℓ) * (discr K).natAbs)
      then Affine.Point.map (W' := Ecurve ℓ) (hy d h.1 h.2).choose.val
        (hy d h.1 h.2).choose_spec.choose else 0
  refine ⟨H, y, ?_⟩
  intro relGal frob
  refine ⟨rfl, rfl, fun d hd hcop => ?_⟩
  dsimp only
  have hH : H d = (hy d hd hcop).choose := dite_eq_left (And.intro hd hcop)
  have hy' : y d = Affine.Point.map (W' := Ecurve ℓ) (hy d hd hcop).choose.val
      (hy d hd hcop).choose_spec.choose := dite_eq_left (And.intro hd hcop)
  constructor
  · let HasPoint (F : IntermediateField ℚ Qbar) : Prop :=
      ∃ Y' : ((Ecurve ℓ).baseChange F).toAffine.Point,
        Affine.Point.map (W' := Ecurve ℓ) F.val Y' = y d
    change HasPoint (H d)
    exact (congrArg HasPoint hH).mpr ⟨(hy d hd hcop).choose_spec.choose, hy'.symm⟩
  · rw [hy']
    exact (hy d hd hcop).choose_spec.choose_spec


end ZInQ.Manuscript.RC.HeegnerAnchor

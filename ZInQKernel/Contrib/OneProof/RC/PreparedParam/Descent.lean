import ZInQKernel.Contrib.OneProof.RC.PreparedParam.Parametrization
import ZInQKernel.Contrib.OneProof.RC.StageSelector.Selector

/-! The evaluation `y = π(x)` in tex 2915–2917 and 8213–8217.
Using the prepared filter and matching the selector's choices are
on-the-spot (c). -/

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField WeierstrassCurve ZInQ.Progressions
  TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory ZInQ.Contrib.CloudB3RC53
  ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd

namespace ZInQ.Manuscript.RC.PreparedParam

open Classical in
/-- Evaluation through a rational morphism carries the CM field of definition
to its image on the elliptic curve, with the same complex embedding. -/
theorem value_of_cmFieldOfDefinition {E : WeierstrassCurve ℚ} [E.IsElliptic]
    [NeZero (newformLevel E)] {X : X0Model (newformLevel E)}
    {f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2}
    {Lat : PeriodPair} {κ : ℂ} (hCM : CMFieldOfDefinition X)
    (hπ : AlgebraicParametrizationAtScale E X f Lat κ)
    {K : Type} [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    (hKC : IsTotallyComplex K) (O : NumberFieldOrder K) {d A B C : ℤ}
    (hO : O.discr = d) (hd : d < 0) (hcop : IsCoprime d (newformLevel E : ℤ))
    (hform : IsHeegnerForm (newformLevel E) d A B C) :
    let H := ringClassField O
    ∃ (ι : H →ₐ[ℚ] ℂ) (y : (E.baseChange H).toAffine.Point),
      Affine.Point.map (W' := E.toAffine) ι y = phiAn E f Lat κ (cmPoint A B d) := by
  obtain ⟨ι, x, hx⟩ := hCM K hK hKC O d A B C hO hd hcop hform
  obtain ⟨π, hπQ, -, hcompat⟩ := hπ
  let u := (x.comp π hπQ).val
  refine ⟨ι, projectiveValue u, ?_⟩
  calc
    _ = projectiveValue (Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ u) :=
      projectiveValue_map ι u
    _ = projectiveValue ((x.map ι).comp π hπQ).val := by
      simp only [u, FieldPoint.comp, FieldPoint.map, Category.assoc]
    _ = _ := (congrArg (fun z : FieldPoint X.overQ ℂ =>
      projectiveValue (z.comp π hπQ).val) hx).trans (hcompat _)

private theorem discr_conductorOne (K : Type) [Field K] [NumberField K] :
    (conductorOrder K 1).discr = discr K := by
  have heq : conductorOrder K 1 = maximalNumberFieldOrder K := by
    ext x
    constructor
    · exact fun hx => conductorOrderSubalgebra_le_integralClosure K 1 hx
    · intro hx
      refine ⟨0, ⟨x, hx⟩, ?_⟩
      simp only [Int.cast_zero, zero_add, Nat.cast_one, one_mul]
      rfl
  rw [heq, NumberFieldOrder.discr_maximal]

private theorem coprime_level {N : ℕ} {d : ℤ}
    (hloc : ∀ p : ℕ, p.Prime → p ∣ 2 * N → SquareAt p d) : IsCoprime d (N : ℤ) := by
  apply Int.isCoprime_iff_gcd_eq_one.mpr
  change d.natAbs.gcd N = 1
  exact Nat.coprime_of_dvd fun p hp hpd hpN =>
    (hloc p hp (dvd_mul_of_dvd_right hpN 2)).1 (Int.natCast_dvd.mpr hpd)

/-- The conductor-one instance uses precisely the quadratic field and
the chosen leading coefficient and middle coefficient of the selector. -/
theorem preparedParamValues {E : WeierstrassCurve ℚ} [E.IsElliptic]
    [NeZero (newformLevel E)] {X : X0Model (newformLevel E)}
    {f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2}
    {Lat : PeriodPair} {κ : ℂ} (hCM : CMFieldOfDefinition X)
    (hπ : AlgebraicParametrizationAtScale E X f Lat κ)
    (hN : 0 < newformLevel E) {hstar : ℤ} (hgp : GenusPartner E hstar) :
    ∀ D (hp : Prepared E hstar D), StageSelector.PreparedParamValue E f Lat κ hN hgp hp := by
  intro D hp
  obtain ⟨hd, hsq, hloc⟩ := StageSelector.prepared_discriminant hp hgp
  have h4 := (hloc 2 Nat.prime_two (dvd_mul_right 2 _)).mod_four
  let _ : Fact (¬ IsSquare ((D * hstar : ℤ) : ℚ)) :=
    ⟨Qsqrt.not_isSquare_of_squarefree hsq (ne_of_lt (hd.trans zero_lt_one))⟩
  let K := Qsqrt (D * hstar)
  have hO : (conductorOrder K 1).discr = D * hstar :=
    (discr_conductorOne K).trans (StageSelector.qsqrt_discr hd hsq h4)
  exact value_of_cmFieldOfDefinition hCM hπ Qsqrt.finrank (Qsqrt.isTotallyComplex hd)
    (conductorOrder K 1) hO hd (coprime_level hloc) (StageSelector.formAtLevel hN hgp hp).property


end ZInQ.Manuscript.RC.PreparedParam

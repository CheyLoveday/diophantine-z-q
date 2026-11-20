import ZInQKernel.Contrib.OneProof.RC.StageSelector.Forms
import ZInQKernel.Contrib.OneProof.RC.StageSelector.Character
import ZInQKernel.Contrib.OneProof.RC.StageMap.Consumers
import ZInQKernel.Contrib.OneProof.RC.Wiring.GenusOdd34

/-! The reference genus points for the stage comparison (tex 8209–8217,
9105–9113, 9272–9291, 9439–9443). The only missing input is the algebraic
realization of the analytic parametrization at the chosen form. Preserving
the existing entries and using a choice independent of the stage are
on-the-spot (c). -/

noncomputable section

open NumberField WeierstrassCurve ZInQ.Progressions TauCeti.ClassFieldTheory
  ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd
  ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.Visibility ZInQ.Manuscript.RC.Stages

namespace ZInQ.Manuscript.RC.StageSelector

section Datum

variable {E : WeierstrassCurve ℚ}
  {f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2}
  {Lat : PeriodPair} {κ : ℂ} {D hstar : ℤ}
  (hN : 0 < newformLevel E) (hgp : GenusPartner E hstar) (hp : Prepared E hstar D)

/-- A chosen primitive form with leading coefficient equal to the level. -/
def formAtLevel :
    {bc : ℤ × ℤ // IsHeegnerForm (newformLevel E) (D * hstar) (newformLevel E) bc.1 bc.2} :=
  let h := prepared_discriminant hp hgp
  let hex := exists_heegnerForm hN h.2.1 h.2.2
  ⟨(hex.choose, hex.choose_spec.choose), hex.choose_spec.choose_spec⟩

include hgp hp in
private theorem not_isSquare_prepared : ¬ IsSquare ((D * hstar : ℤ) : ℚ) :=
  Qsqrt.not_isSquare_of_squarefree (prepared_discriminant hp hgp).2.1
    (ne_of_lt ((prepared_discriminant hp hgp).1.trans zero_lt_one))

open Classical in
/-- The single missing CM input: the analytic value at the chosen form of
discriminant `D*hstar` is the image of a point over its conductor-one ring
class field under a complex embedding. The quadratic field, form, and
character are constructed separately. -/
def PreparedParamValue (E : WeierstrassCurve ℚ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2)
    (Lat : PeriodPair) (κ : ℂ) {D hstar : ℤ}
    (hN : 0 < newformLevel E) (hgp : GenusPartner E hstar) (hp : Prepared E hstar D) : Prop :=
  letI : Fact (¬ IsSquare ((D * hstar : ℤ) : ℚ)) := ⟨not_isSquare_prepared hgp hp⟩
  let H := ringClassField (conductorOrder (Qsqrt (D * hstar)) 1)
  ∃ (ι : H →ₐ[ℚ] ℂ) (y : (E.baseChange H).toAffine.Point),
    Affine.Point.map (W' := E.toAffine) ι y =
      phiAn E f Lat κ (cmPoint (newformLevel E) (formAtLevel hN hgp hp).val.1 (D * hstar))

set_option maxRecDepth 1024 in
/-- The same constructor fields as in the fixed witness datum, at any
prepared parameter with the indicated algebraic parametrization value. -/
def datumOfPrepared (halg : PreparedParamValue E f Lat κ hN hgp hp) :
    HeegnerDatum E f Lat κ (D * hstar) 1 hstar := by
  classical
  letI : Fact (¬ IsSquare ((D * hstar : ℤ) : ℚ)) := ⟨not_isSquare_prepared hgp hp⟩
  let K := Qsqrt (D * hstar)
  have h := prepared_discriminant hp hgp
  have hD := (hp.2.2.1 2 Nat.prime_two (dvd_mul_right 2 _)).mod_four
  have hh8 := (hgp.2.2.2.2.1 2 Nat.prime_two (dvd_mul_right 2 _)).2.1 rfl
  have h4 := (h.2.2 2 Nat.prime_two (dvd_mul_right 2 _)).mod_four
  have hKC : IsTotallyComplex K := Qsqrt.isTotallyComplex h.1
  have hKu : (QuadraticAlgebra.omega : K) ^ 2 = ((D * hstar : ℤ) : K) := by
    exact Qsqrt.ringHom_omega_sq (RingHom.id K)
  let hs := sqrt_mem_conductorOne hKC hD hgp.2.1 hp.2.2.2 hKu
  let hχ := exists_genusCharacter hh8 hs.choose_spec
  unfold PreparedParamValue at halg
  refine
    { K := K
      finrank_two := Qsqrt.finrank
      totallyComplex := hKC
      disc := qsqrt_discr h.1 h.2.1 h4
      χ := hχ.choose
      quad := hχ.choose_spec
      prim := fun c' _ hc' hne => (hne (Nat.dvd_one.mp hc')).elim
      A := newformLevel E
      B := (formAtLevel hN hgp hp).val.1
      C := (formAtLevel hN hgp hp).val.2
      form := by simpa only [one_pow, Int.natCast_one, mul_one] using
        (formAtLevel hN hgp hp).property
      ι := halg.choose
      y := halg.choose_spec.choose
      hy := by simpa only [one_pow, Int.natCast_one, mul_one] using halg.choose_spec.choose_spec }

end Datum

section Select

variable {ℓ : ℕ} {W : WData ℓ} (I : GenusOddInstance W) {Dw : ℤ}
  (dat : HeegnerDatum (Ecurve ℓ) I.f I.Lat I.κ (Dw * W.hstar) 1 W.hstar)
  (hglue : PreparedGlue W)

include dat in
private theorem level_pos_of_witness : 0 < newformLevel (Ecurve ℓ) := by
  by_contra! hN
  have h0 : newformLevel (Ecurve ℓ) = 0 := Nat.eq_zero_of_le_zero hN
  have hA : dat.A = 0 := by
    have h := dat.form.2.1
    simpa [h0] using h
  exact (ne_of_gt dat.form.1) hA

include I hglue in
private theorem preparedAt {D : ℤ} (h : ∃ θ, W.admissible θ D) :
    Prepared (Ecurve ℓ) W.hstar D :=
  I.hprep D (hglue _ D h.choose_spec)

variable (halg : ∀ D (h : ∃ θ, W.admissible θ D), D ≠ Dw → I.selG D = none →
  PreparedParamValue (Ecurve ℓ) I.f I.Lat I.κ (level_pos_of_witness I dat) I.hgp
    (preparedAt I hglue h))

open Classical in
/-- Extend only holes that occur at admissible nonwitness parameters. Every
existing choice is kept, in particular the datum and embedding used by the
witness calculation. -/
def extendSelG (D : ℤ) : Option (HeegnerDatum (Ecurve ℓ) I.f I.Lat I.κ (D * W.hstar) 1 W.hstar) :=
  if hold : I.selG D = none then
    if h : ∃ θ, W.admissible θ D then
      if hD : D ≠ Dw then some (datumOfPrepared (level_pos_of_witness I dat) I.hgp
        (preparedAt I hglue h) (halg D h hD hold))
      else none
    else none
  else I.selG D

/-- The existing genus entries survive extension verbatim. -/
theorem extendSelG_eq_some {D : ℤ}
    {t : HeegnerDatum (Ecurve ℓ) I.f I.Lat I.κ (D * W.hstar) 1 W.hstar}
    (ht : I.selG D = some t) : extendSelG I dat hglue halg D = some t := by
  simp [extendSelG, ht]

/-- The new selector uses the same fixed witness entry. -/
theorem extendSelG_witness (hdat : I.selG Dw = some dat) :
    extendSelG I dat hglue halg Dw = some dat :=
  extendSelG_eq_some I dat hglue halg hdat

/-- The missing row of the stage-map assembly, for the extended selector. -/
theorem extendSelG_isSome_of_admissible {θ : ℕ} {D : ℤ} (h : W.admissible θ D) (hne : D ≠ Dw) :
    (extendSelG I dat hglue halg D).isSome := by
  cases hold : I.selG D with
  | some t => simp [extendSelG_eq_some I dat hglue halg hold]
  | none => simp [extendSelG, hold, show ∃ j, W.admissible j D from ⟨θ, h⟩, hne]

/-- Supply the exact selection equation consumed by
`StageMap.lamOf_admissible`. -/
theorem exists_selected_of_admissible (hdat : I.selG Dw = some dat)
    {θ : ℕ} {D : ℤ} (h : W.admissible θ D) :
    ∃ t, extendSelG I dat hglue halg D = some t := by
  by_cases hD : D = Dw
  · subst D
    exact ⟨dat, extendSelG_witness I dat hglue halg hdat⟩
  · exact Option.isSome_iff_exists.mp (extendSelG_isSome_of_admissible I dat hglue halg h hD)

/-- The index read by (3.4) is unchanged at every prepared simple zero. -/
theorem jgen_extendSelG_at_simpleZero {D : ℤ} (hp : W.prepared D)
    (hz : AnalyticRank (qtwist (Ecurve ℓ) D) 1) :
    jgenOf (Ecurve ℓ) I.f I.Lat I.κ W.hstar (extendSelG I dat hglue halg) D = W.jgen D := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (I.hselG D (I.hprep D hp) hz)
  rw [I.hjg]
  simp only [jgenOf, ht, extendSelG_eq_some I dat hglue halg ht]

end Select

/-- For actual stages the prepared-filter bridge is a projection of the
existing stage construction. -/
theorem preparedGlue_of_withStages {ℓ : ℕ} {W : WData ℓ} {At : ℕ → ℕ → Prop}
    {cw : ℕ} {B : Finset ℕ} {q : StageSequence At cw B} (hs : withStages W q W.prepared = W) :
    PreparedGlue W := by
  intro θ D h
  exact (show W.prepared D ∧ stageTest q θ D from
    (congrArg (fun V : WData ℓ => V.admissible θ D) hs).mpr h).1


end ZInQ.Manuscript.RC.StageSelector

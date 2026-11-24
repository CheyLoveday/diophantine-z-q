import ZInQKernel.Contrib.OneProof.RC.StageKummer.Actual

/-! The comparison uses the integral presentation of the same map (c). -/

noncomputable section

open WeierstrassCurve NumberField TauCeti TauCeti.ClassFieldTheory
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.GenusOdd
open ZInQ.Manuscript.RC.PrintsArith ZInQ.Manuscript.RC.Stages
  ZInQ.Manuscript.RC.Visibility ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.WitnessSpec
open scoped WeierstrassCurve Classical

set_option linter.style.haveILetI false

namespace ZInQ.Manuscript.RC.StageKummer

open PMGeometry

section Composition

variable {C : WeierstrassCurve ℤ}
  {f : CuspForm (CongruenceSubgroup.Gamma0 (CST.newformLevel (C⁄ℚ)) :
    Subgroup (GL (Fin 2) ℝ)) 2} {Lat : PeriodPair} {κ : ℂ} {hstar D : ℤ}
  {g : GalQ} {p M : ℕ} [Fact p.Prime] [(ReducedEquation C p).IsElliptic]

/-- The explicit composite, with the point structure used by StageKummer. -/
def datumComposite (t : HeegnerDatum (C⁄ℚ) f Lat κ (D * hstar) 1 hstar)
    (v : FrobeniusPlace g p) (loc : DatumPlace t v) (hg : ¬ (p : ℤ) ∣ C.Δ)
    (d : PM.Evaluation (ResidueAt v) (ReducedEquation C p) M) :
    letI := Classical.decEq (DatumField t)
    DatumPoints t →+ ZMod (2 ^ M) :=
  letI := Classical.decEq (DatumField t)
  (PM.lam d).comp (datumReduction t v loc hg)

end Composition

variable {E : WeierstrassCurve ℚ} {C : WeierstrassCurve ℤ} (hE : C⁄ℚ = E)
  {f : CuspForm (CongruenceSubgroup.Gamma0 (CST.newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2}
  {Lat : PeriodPair} {κ : ℂ} {hstar : ℤ}

variable [E.IsElliptic] (h₁ : E.a₁ = 0) (h₃ : E.a₃ = 0)
  {Dw : ℤ} (dat : HeegnerDatum E f Lat κ (Dw * hstar) 1 hstar)
  {L : ℕ} (w : ExactWitnessOn E h₁ h₃ dat L)
  [(qtwist E (Dw : ℚ)).IsElliptic] {Q : GeomPoint (qtwist E (Dw : ℚ))}
  (hQw : Q = rationalGeomPoint (qtwist E (Dw : ℚ)) w.rational)
  {a : ℕ} {S : Finset ℕ} {F₀ : IntermediateField ℚ Qbar} {σ : GalQ}
  (q : StageSequence (ActualAt (qtwist E (Dw : ℚ)) E Q F₀ σ Dw hstar) (a + 1) S)

variable (hσ : tateRep E 2 (σ * σ) = 1)
  (emb : StageMap.DatumEmbeddings E f Lat κ hstar)
  (b : TateMod (qtwist E (Dw : ℚ)) 2 →ₗ[ℤ_[2]] ℤ_[2])
  (hb : ∀ t, b (tateRep (qtwist E (Dw : ℚ)) 2 σ t) = b t)
  {Mθ : ℕ → ℕ} (hM : Mθ = fun i => a + 1 + 1 + i)
  (i : ℕ) {D : ℤ} (t : HeegnerDatum E f Lat κ (D * hstar) 1 hstar) (hs : stageTest q i D)

set_option maxHeartbeats 500000 in
/-- Supply hev of lamOf_reduction_at at the selected place and precision.
The statement applies even before a selector chooses the datum. -/
theorem evActual_eq_comp :
    letI : Fact (q.stage i).p.Prime := ⟨(q.stage i).prime⟩
    letI := StageIdent.selectedCurveOn_elliptic C hE h₁ h₃ dat w hQw q i
    evOnModel hE (evActual hE h₁ h₃ dat w hQw q hσ emb b hM) i D (datumOnModel hE t) =
      datumComposite (C := C) (M := Mθ i) (datumOnModel hE t)
        (FrobeniusPlace.ofIsFrobAt (selectedFrobenius q i).property.1)
        (datumPlaceOn hE h₁ h₃ dat w hQw q emb i t hs) (stageGood hE h₁ h₃ dat w hQw q i)
        (StageIdent.selectedEvaluationOn C hE h₁ h₃ dat w hQw q hσ b hb hM i) := by
  subst hE hQw hM
  dsimp +instances only [evOnModel, evActual, StageMap.actualEvaluationsOn, datumOnModel, formOnModel,
    datumComposite, datumPlaceOn, StageIdent.selectedEvaluationOn]
  have he := ev_eq_comp C h₁ h₃ (f := f) (Lat := Lat) (κ := κ) (hstar := hstar)
    (Dw := Dw) dat (L := L) w (a := a) (S := S) (F₀ := F₀) (σ := σ) q hσ emb b hb i (D := D) t hs
  exact he

end ZInQ.Manuscript.RC.StageKummer

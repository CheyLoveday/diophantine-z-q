import ZInQKernel.Contrib.OneProof.RC.PMGeometry.Heegner
import ZInQKernel.Contrib.OneProof.RC.StageIdent.Detector

/-! Tex 8378–8398, 8439–8456, 9205–9209 and 9265–9291: contract the
detector's absolute place to the conductor-one field, then apply the detector.
The transports between the integral model and the wiring are on-the-spot (c). -/

noncomputable section

open WeierstrassCurve NumberField TauCeti TauCeti.ClassFieldTheory
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.GenusOdd
open ZInQ.Manuscript.RC.PrintsArith ZInQ.Manuscript.RC.Stages
  ZInQ.Manuscript.RC.Visibility ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.WitnessSpec
open scoped WeierstrassCurve Classical

set_option linter.style.haveILetI false

namespace ZInQ.Manuscript.RC.StageKummer

open PMGeometry

section Embeddings

variable {E : WeierstrassCurve ℚ}
  {f : CuspForm (CongruenceSubgroup.Gamma0 (CST.newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2}
  {Lat : PeriodPair} {κ : ℂ} {hstar : ℤ}

abbrev RingClassAt {D : ℤ} (t : HeegnerDatum E f Lat κ (D * hstar) 1 hstar) :=
  letI := t.field; letI := t.nf; letI := t.nz
  ringClassField (CST.conductorOrder t.K 1)

/-- Factor the complex realization of the datum through the algebraic numbers. -/
def complexAlgebraic {D : ℤ} (t : HeegnerDatum E f Lat κ (D * hstar) 1 hstar) :
    letI := t.field; letI := t.nf; letI := t.nz
    RingClassAt t →ₐ[ℚ] algebraicClosure ℚ ℂ := by
  letI := t.field; letI := t.nf; letI := t.nz
  exact AlgHom.codRestrict t.ι (algebraicClosure ℚ ℂ).toSubalgebra fun x =>
    (map_mem_algebraicClosure_iff t.ι).mpr
      (mem_algebraicClosure_iff.mpr (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x))

variable {h₁ : E.a₁ = 0} {h₃ : E.a₃ = 0} {Dw : ℤ}
  {dat : HeegnerDatum E f Lat κ (Dw * hstar) 1 hstar} {L : ℕ}
  (w : ExactWitnessOn E h₁ h₃ dat L)

private def closureEquivOver {H : Type} [Field H] [Algebra ℚ H]
    (e : H →ₐ[ℚ] Qbar) (f : H →ₐ[ℚ] algebraicClosure ℚ ℂ) :
    {g : Qbar ≃ₐ[ℚ] algebraicClosure ℚ ℂ // ∀ x, g (e x) = f x} := by
  letI : IsAlgClosed (algebraicClosure ℚ ℂ) := IsAlgClosure.isAlgClosed ℚ
  letI : Algebra H Qbar := e.toRingHom.toAlgebra
  letI : IsScalarTower ℚ H Qbar := .of_algebraMap_eq fun x => (e.commutes x).symm
  letI : Algebra.IsAlgebraic H Qbar := Algebra.IsAlgebraic.tower_top (K := ℚ) H
  let h := Classical.indefiniteDescription _
    (IsAlgClosed.surjective_domRestrict_of_isAlgebraic
      (K := ℚ) (L := H) (E := Qbar) (M := algebraicClosure ℚ ℂ) f)
  let back : algebraicClosure ℚ ℂ →ₐ[ℚ] Qbar := IsAlgClosed.lift
  exact ⟨AlgEquiv.ofBijective h.val (Algebra.IsAlgebraic.algHom_bijective₂ h.val back).1,
    fun x => DFunLike.congr_fun h.property x⟩

/-- Fix one identification of the two algebraic closures over the witness
field, so the witness's given algebraic and complex embeddings agree. -/
def witnessComplex :
    {e : Qbar ≃ₐ[ℚ] algebraicClosure ℚ ℂ //
      letI := dat.field; letI := dat.nf; letI := dat.nz
      ∀ x : RingClassAt dat, e (w.emb x) = complexAlgebraic dat x} := by
  letI := dat.field; letI := dat.nf; letI := dat.nz
  exact closureEquivOver w.emb (complexAlgebraic dat)

/-- Use the same complex realization of the absolute closure at all
parameters, with the original complex embedding of each datum. -/
def witnessEmbeddings : StageMap.DatumEmbeddings E f Lat κ hstar :=
  fun _ t => (witnessComplex w).val.symm.toAlgHom.comp (complexAlgebraic t)

theorem witnessEmbeddings_at_witness :
    witnessEmbeddings w Dw dat = w.emb := by
  letI := dat.field; letI := dat.nf; letI := dat.nz
  ext x
  apply (witnessComplex w).val.injective
  exact ((witnessComplex w).val.apply_symm_apply _).trans ((witnessComplex w).property x).symm

/-- The embedding used for the contraction represents the given complex
datum, including at the anchored witness. -/
theorem anchoredEmbeddings_complex {D : ℤ}
    (t : HeegnerDatum E f Lat κ (D * hstar) 1 hstar) :
    letI := t.field; letI := t.nf; letI := t.nz
    ∀ x : RingClassAt t,
      (witnessComplex w).val (StageMap.anchoredEmbeddings w (witnessEmbeddings w) D t x) =
        complexAlgebraic t x := by
  have h : StageMap.anchoredEmbeddings w (witnessEmbeddings w) D t = witnessEmbeddings w D t := by
    by_cases hD : D = Dw
    · subst D
      by_cases ht : t = dat
      · subst t
        rw [StageMap.anchoredEmbeddings_witness, witnessEmbeddings_at_witness]
      · simp [StageMap.anchoredEmbeddings, ht]
    · simp [StageMap.anchoredEmbeddings, hD]
  exact fun x => by
    rw [h]
    exact (witnessComplex w).val.apply_symm_apply _

end Embeddings

section Integral

variable (C : WeierstrassCurve ℤ) [(C⁄ℚ).IsElliptic]
  (h₁ : (C⁄ℚ).a₁ = 0) (h₃ : (C⁄ℚ).a₃ = 0)
  {f : CuspForm (CongruenceSubgroup.Gamma0 (CST.newformLevel (C⁄ℚ)) : Subgroup (GL (Fin 2) ℝ)) 2}
  {Lat : PeriodPair} {κ : ℂ} {hstar Dw : ℤ}
  (dat : HeegnerDatum (C⁄ℚ) f Lat κ (Dw * hstar) 1 hstar)
  {L : ℕ} (w : ExactWitnessOn (C⁄ℚ) h₁ h₃ dat L)
  [(qtwist (C⁄ℚ) (Dw : ℚ)).IsElliptic] {a : ℕ} {S : Finset ℕ}
  {F₀ : IntermediateField ℚ Qbar} {σ : GalQ}
  (q : StageSequence (ActualAt (qtwist (C⁄ℚ) (Dw : ℚ)) (C⁄ℚ)
    (rationalGeomPoint (qtwist (C⁄ℚ) (Dw : ℚ)) w.rational) F₀ σ Dw hstar) (a + 1) S)
  (hσ : tateRep (C⁄ℚ) 2 (σ * σ) = 1)
  (emb : StageMap.DatumEmbeddings (C⁄ℚ) f Lat κ hstar)
  (b : TateMod (qtwist (C⁄ℚ) (Dw : ℚ)) 2 →ₗ[ℤ_[2]] ℤ_[2])
  (hb : ∀ t, b (tateRep (qtwist (C⁄ℚ) (Dw : ℚ)) 2 σ t) = b t)
  (i : ℕ) {D : ℤ} (t : HeegnerDatum (C⁄ℚ) f Lat κ (D * hstar) 1 hstar)
  (hs : stageTest q i D)

include emb hs in
/-- Use the datum's fixed realization in the absolute closure carrying the
detector place, with the exact witness embedding at the witness. -/
def datumPlace :
    letI : Fact (q.stage i).p.Prime := ⟨(q.stage i).prime⟩
    DatumPlace t (PMGeometry.selectedPlace q i) := by
  letI : Fact (q.stage i).p.Prime := ⟨(q.stage i).prime⟩
  exact ⟨StageMap.anchoredEmbeddings w emb D t, (StageMap.stage_disc_of_test C h₁ h₃ dat w q i t hs).2⟩

/-- The prime on the datum's field lies above the detector's rational prime. -/
theorem datumPlace_under :
    letI : Fact (q.stage i).p.Prime := ⟨(q.stage i).prime⟩
    letI := t.field; letI := t.nf; letI := t.nz
    ((PMGeometry.selectedPlace q i).restrictPrime
      (datumPlace C h₁ h₃ dat w q emb i t hs).emb).under ℤ =
      Ideal.span {((q.stage i).p : ℤ)} := by
  letI : Fact (q.stage i).p.Prime := ⟨(q.stage i).prime⟩
  letI := t.field; letI := t.nf; letI := t.nz
  exact (PMGeometry.selectedPlace q i).restrictPrime_under (datumPlace C h₁ h₃ dat w q emb i t hs).emb

/-- Contracting the ring class prime to the quadratic base gives the
restriction of the very same detector place. -/
theorem datumPlace_liesOver :
    letI : Fact (q.stage i).p.Prime := ⟨(q.stage i).prime⟩
    letI := t.field; letI := t.nf; letI := t.nz
    let e := (datumPlace C h₁ h₃ dat w q emb i t hs).emb
    ((PMGeometry.selectedPlace q i).restrictPrime e).LiesOver
      ((PMGeometry.selectedPlace q i).restrictPrime
        (e.comp (IsScalarTower.toAlgHom ℚ t.K (DatumField t)))) := by
  letI : Fact (q.stage i).p.Prime := ⟨(q.stage i).prime⟩
  letI := t.field; letI := t.nf; letI := t.nz
  exact (PMGeometry.selectedPlace q i).restrictPrime_liesOver
    (datumPlace C h₁ h₃ dat w q emb i t hs).emb

/-- The two ring class reductions are constructed from the same embedding
and the same absolute place; the different inertness proofs are immaterial. -/
theorem datumReduction_eq :
    letI : Fact (q.stage i).p.Prime := ⟨(q.stage i).prime⟩
    letI := Classical.decEq (DatumField t)
    datumReduction t (PMGeometry.selectedPlace q i) (datumPlace C h₁ h₃ dat w q emb i t hs)
      (stage_facts C h₁ h₃ dat w q i).2.1 =
      StageMap.ringClassRed C h₁ h₃ dat w q hσ emb i t hs := rfl

/-- At the witness the reduction uses exactly the witness embedding, so
its homomorphism is the reduction in the existing witness pin. -/
theorem datumReduction_witness :
    letI : Fact (q.stage i).p.Prime := ⟨(q.stage i).prime⟩
    letI := Classical.decEq (DatumField dat)
    datumReduction dat (PMGeometry.selectedPlace q i)
      (datumPlace C h₁ h₃ dat w q emb i dat (witness_on_stages q i))
      (stage_facts C h₁ h₃ dat w q i).2.1 = actualRingClassRed C h₁ h₃ dat w q hσ i := by
  letI : Fact (q.stage i).p.Prime := ⟨(q.stage i).prime⟩
  rw [datumReduction_eq C h₁ h₃ dat w q hσ emb i dat (witness_on_stages q i)]
  unfold StageMap.ringClassRed actualRingClassRed
  simp only [StageMap.anchoredEmbeddings_witness, StageMap.selectedPlace]

set_option maxHeartbeats 1200000 in
/-- The hev premise of lamOf_reduction_at on the integral model, at every
datum on the moving split support. The selectedEvaluation_lam theorem
compares the whole residue homomorphism using inverse specialization of
the split twist torsion (the twisted analogue of stageMap_eq_lam_comp). -/
theorem ev_eq_comp :
    letI : Fact (q.stage i).p.Prime := ⟨(q.stage i).prime⟩
    letI := Classical.decEq (DatumField t)
    letI := StageIdent.selectedCurve_elliptic C h₁ h₃ dat w q i
    (StageMap.actualEvaluations C h₁ h₃ dat w q hσ emb b).ev i D t =
      (PM.lam (StageIdent.selectedEvaluation C h₁ h₃ dat w q hσ b hb i)).comp
        (datumReduction t (PMGeometry.selectedPlace q i) (datumPlace C h₁ h₃ dat w q emb i t hs)
          (stage_facts C h₁ h₃ dat w q i).2.1) := by
  letI : Fact (q.stage i).p.Prime := ⟨(q.stage i).prime⟩
  letI := StageIdent.selectedCurve_elliptic C h₁ h₃ dat w q i
  rw [StageMap.Evaluations.ev_of_support _ i D t hs,
    StageIdent.selectedEvaluation_lam C h₁ h₃ dat w q hσ b hb i emb]
  exact congrArg _ (datumReduction_eq C h₁ h₃ dat w q hσ emb i t hs).symm

/-- At the fixed witness the detector uses the same row, transported
through the same split-twist torsion identification as actualStageMap. -/
theorem witness_detector :
    letI : Fact (q.stage i).p.Prime := ⟨(q.stage i).prime⟩
    letI := Classical.decEq (DatumField dat)
    letI := StageIdent.selectedCurve_elliptic C h₁ h₃ dat w q i
    actualStageMap C h₁ h₃ dat w q hσ b i Dw dat =
      (PM.lam (StageIdent.selectedEvaluation C h₁ h₃ dat w q hσ b hb i)).comp
        (datumReduction dat (PMGeometry.selectedPlace q i)
          (datumPlace C h₁ h₃ dat w q emb i dat (witness_on_stages q i))
          (stage_facts C h₁ h₃ dat w q i).2.1) := by
  letI : Fact (q.stage i).p.Prime := ⟨(q.stage i).prime⟩
  letI := StageIdent.selectedCurve_elliptic C h₁ h₃ dat w q i
  rw [← ev_eq_comp C h₁ h₃ dat w q hσ emb b hb i dat (witness_on_stages q i)]
  exact (StageMap.actualEvaluations_at_witness C h₁ h₃ dat w q hσ emb b i).symm

end Integral

section Model

variable {E : WeierstrassCurve ℚ} {C : WeierstrassCurve ℤ} (hE : C⁄ℚ = E)
  {f : CuspForm (CongruenceSubgroup.Gamma0 (CST.newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2}
  {Lat : PeriodPair} {κ : ℂ} {hstar : ℤ}

def formOnModel :
    CuspForm (CongruenceSubgroup.Gamma0 (CST.newformLevel (C⁄ℚ)) : Subgroup (GL (Fin 2) ℝ)) 2 := by
  subst E
  exact f

def datumOnModel {D : ℤ} (t : HeegnerDatum E f Lat κ (D * hstar) 1 hstar) :
    HeegnerDatum (C⁄ℚ) (formOnModel (f := f) hE) Lat κ (D * hstar) 1 hstar := by
  subst E
  exact t

def selectorOnModel
    (selG : (D : ℤ) → Option (HeegnerDatum E f Lat κ (D * hstar) 1 hstar)) :
    (D : ℤ) → Option (HeegnerDatum (C⁄ℚ) (formOnModel (f := f) hE) Lat κ (D * hstar) 1 hstar) :=
  fun D => (selG D).map (datumOnModel hE)

def evOnModel {Mθ : ℕ → ℕ} (ev : Visibility.StageKummer E f Lat κ hstar Mθ) :
    Visibility.StageKummer (C⁄ℚ) (formOnModel (f := f) hE) Lat κ hstar Mθ := by
  subst E
  exact ev

theorem selectorOnModel_some
    {selG : (D : ℤ) → Option (HeegnerDatum E f Lat κ (D * hstar) 1 hstar)}
    {D : ℤ} {t : HeegnerDatum E f Lat κ (D * hstar) 1 hstar} (ht : selG D = some t) :
    selectorOnModel hE selG D = some (datumOnModel hE t) := by
  simp only [selectorOnModel, ht, Option.map_some]

theorem lamOf_onModel (Mθ : ℕ → ℕ) (L : ℕ)
    (selG : (D : ℤ) → Option (HeegnerDatum E f Lat κ (D * hstar) 1 hstar))
    (ev : Visibility.StageKummer E f Lat κ hstar Mθ) (i : ℕ) (D : ℤ) :
    lamOf Mθ L (selectorOnModel hE selG) (evOnModel hE ev) i D = lamOf Mθ L selG ev i D := by
  subst E
  cases h : selG D <;> simp [selectorOnModel, datumOnModel, evOnModel, lamOf, h]

variable [E.IsElliptic] (h₁ : E.a₁ = 0) (h₃ : E.a₃ = 0)
  {Dw : ℤ} (dat : HeegnerDatum E f Lat κ (Dw * hstar) 1 hstar)
  {L : ℕ} (w : ExactWitnessOn E h₁ h₃ dat L)
  [(qtwist E (Dw : ℚ)).IsElliptic] {Q : GeomPoint (qtwist E (Dw : ℚ))}
  (hQw : Q = rationalGeomPoint (qtwist E (Dw : ℚ)) w.rational)
  {a : ℕ} {S : Finset ℕ} {F₀ : IntermediateField ℚ Qbar} {σ : GalQ}
  (q : StageSequence (ActualAt (qtwist E (Dw : ℚ)) E Q F₀ σ Dw hstar) (a + 1) S)

include hE hQw in
theorem stageGood (i : ℕ) :
    ¬ ((q.stage i).p : ℤ) ∣ C.Δ := by
  subst hE hQw
  exact (stage_facts C h₁ h₃ dat w q i).2.1

def datumPlaceOn (emb : StageMap.DatumEmbeddings E f Lat κ hstar)
    (i : ℕ) {D : ℤ} (t : HeegnerDatum E f Lat κ (D * hstar) 1 hstar) (hs : stageTest q i D) :
    letI : Fact (q.stage i).p.Prime := ⟨(q.stage i).prime⟩
    DatumPlace (datumOnModel hE t) (FrobeniusPlace.ofIsFrobAt (selectedFrobenius q i).property.1) := by
  subst hE hQw
  exact datumPlace C h₁ h₃ dat w q emb i t hs

variable (hσ : tateRep E 2 (σ * σ) = 1)
  (emb : StageMap.DatumEmbeddings E f Lat κ hstar)
  (b : TateMod (qtwist E (Dw : ℚ)) 2 →ₗ[ℤ_[2]] ℤ_[2])
  (hb : ∀ t, b (tateRep (qtwist E (Dw : ℚ)) 2 σ t) = b t)
  {Mθ : ℕ → ℕ} (hM : Mθ = fun i => a + 1 + 1 + i)
  (i : ℕ) {D : ℤ} (t : HeegnerDatum E f Lat κ (D * hstar) 1 hstar) (hs : stageTest q i D)

/-- The shared family on the wiring curve. Its off-support entries are zero
by Evaluations.ev; no claim about reduction is made there. -/
abbrev evActual :=
  (StageMap.actualEvaluationsOn C hE h₁ h₃ dat w hQw q hσ emb b hM).ev

/-- The total family uses the zero homomorphism at unused entries. -/
theorem evActual_off_support (h : ¬ stageTest q i D) :
    evActual hE h₁ h₃ dat w hQw q hσ emb b hM i D t = 0 := by
  unfold evActual StageMap.Evaluations.ev
  exact dite_eq_right h

include hb in
/-- The witness agreement required by OddStagedInstance.hev. -/
theorem evActual_witness :
    evActual hE h₁ h₃ dat w hQw q hσ emb b hM i Dw dat =
      actualStageMapOn C hE h₁ h₃ dat w hQw q hσ b hM i Dw dat := by
  subst E Q Mθ
  exact (ev_eq_comp C h₁ h₃ dat w q hσ emb b hb i dat (witness_on_stages q i)).trans
    (witness_detector C h₁ h₃ dat w q hσ emb b hb i).symm

end Model

end ZInQ.Manuscript.RC.StageKummer

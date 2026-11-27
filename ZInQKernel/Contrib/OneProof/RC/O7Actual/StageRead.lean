import ZInQKernel.Contrib.OneProof.RC.StageMap.Consumers

/-! Read the selected reduction at the precision of the actual stage. -/

noncomputable section

open WeierstrassCurve TauCeti.ClassFieldTheory
open scoped WeierstrassCurve
open ZInQ.Manuscript.RC.Visibility
open ZInQ.Contrib.CloudB3RC53.GenusOdd

namespace ZInQ.Manuscript.RC.O7Actual

open ZInQ.Manuscript.RC.PrintsArith ZInQ.Manuscript.RC.Stages ZInQ.Manuscript.RC.Wiring
open ZInQ.Contrib.CloudB3RC53
open StageMap

variable {ℓ : ℕ} (W : WData ℓ) [(Ecurve ℓ).IsElliptic]
  {f : CuspForm (CongruenceSubgroup.Gamma0 (CST.newformLevel (Ecurve ℓ)) : Subgroup (GL (Fin 2) ℝ)) 2}
  {Lat : PeriodPair} {κ : ℂ} {Dw : ℤ}
  (dat : HeegnerDatum (Ecurve ℓ) f Lat κ (Dw * W.hstar) 1 W.hstar)
  {L : ℕ} (w : ExactWitnessOn (Ecurve ℓ) rfl rfl dat L)
  [(qtwist (Ecurve ℓ) (Dw : ℚ)).IsElliptic] {Q : GeomPoint (qtwist (Ecurve ℓ) (Dw : ℚ))}
  (hQw : Q = WitnessSpec.rationalGeomPoint (qtwist (Ecurve ℓ) (Dw : ℚ)) w.rational)
  {a : ℕ} {S : Finset ℕ} {F₀ : IntermediateField ℚ Qbar} {σ : GalQ}
  (q : StageSequence (ActualAt (qtwist (Ecurve ℓ) (Dw : ℚ)) (Ecurve ℓ) Q F₀ σ Dw W.hstar) (a + 1) S)
  (hσ : tateRep (Ecurve ℓ) 2 (σ * σ) = 1)
  (emb : DatumEmbeddings (Ecurve ℓ) f Lat κ W.hstar)
  (b : TateMod (qtwist (Ecurve ℓ) (Dw : ℚ)) 2 →ₗ[ℤ_[2]] ℤ_[2])
  (hstages : withStages W q W.prepared = W)
  (selG : (D : ℤ) → Option (HeegnerDatum (Ecurve ℓ) f Lat κ (D * W.hstar) 1 W.hstar))

/-- Tex 9283–9291: on the actual admissible domain, the reference congruence
against `lamOf` is the congruence against the read of the reduced scaled
genus point. This is a change of the right-hand-side description only. -/
theorem actual_reference_read {O : Type*} [CommRing O] {i : ℕ} {D : ℤ}
    (t : HeegnerDatum (Ecurve ℓ) f Lat κ (D * W.hstar) 1 W.hstar)
    (ht : selG D = some t) (hd : W.admissible i D) (value : O) :
    letI := t.field; letI := t.nf; letI := t.nz
    letI := Classical.decEq (ringClassField (CST.conductorOrder t.K 1))
    let E := actualForStages W dat w hQw q hσ emb b hstages
    ((2 : O) ^ W.Mθ i ∣ value - (lamOf W.Mθ L selG E.ev i D : O)) ↔
    (2 : O) ^ W.Mθ i ∣ value -
      (((E.eval i (E.reduction i D t (admissible_stageTest W hstages hd)
        (L • genusPoint t))).val : ℤ) : O) := by
  dsimp only
  exact Iff.of_eq (congrArg (fun n : ℤ => (2 : O) ^ W.Mθ i ∣ value - (n : O))
    (lamOf_admissible W dat w hQw q hσ emb b hstages selG t ht hd))

end ZInQ.Manuscript.RC.O7Actual

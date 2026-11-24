import ZInQKernel.Contrib.OneProof.RC.StageKummer.Reference

/-! Pass the reference records through the existing orbit comparison and
into the odd wiring. The phase is read from each reference tuple (c). -/

noncomputable section

open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.GenusOdd
open ZInQ.Manuscript.RC.Visibility ZInQ.Manuscript.RC.Wiring
open scoped Classical

namespace ZInQ.Manuscript.RC.StageKummer

open O7Actual Visibility.ThetaStage

private def coreOfDatum {O : Type} [CommRing O] {N M : ℕ} {hN : 0 < N} {m D lam : ℤ}
    {S : StageAt O N M hN m} (A : DatumAt S D lam)
    (contract : ∀ n : ℤ, (2 : O) ^ M ∣ (n : O) → (2 : ℤ) ^ M ∣ n) (aθ : ℤ)
    (ha : (2 : O) ^ M ∣ A.weights.phase A.reference * (aθ : O) -
      thetaCoeff S.visibility ((((S.weights.m : ℤ) * D : ℤ) : ℚ))) :
    ComparisonCore S.visibility M m D N.primeFactors.card lam (A.weights.phase A.reference) := by
  let inputs := O7Actual.comparisonInputs S.weights S.hu A.orbits A.weights A.moves
    A.reference A.reduce A.support.stabilizer contract aθ ha
  exact cast (congrArg (fun m' : ℤ => ComparisonCore S.visibility M m' D N.primeFactors.card
    lam (A.weights.phase A.reference)) S.m_eq) inputs.toCore

variable {ℓ : ℕ} {W : WData ℓ} {I : GenusOddInstance W} {L : ℕ} (s : Setup I L)
  {O : Type} [CommRing O] {N : ℕ} {hN : 0 < N}
  (S : ∀ i, StageAt O N (W.Mθ i) hN (-W.hstar))
  (A : ∀ i D, W.admissible i D → DatumAt (S i) D (lamOf W.Mθ L I.selG s.ev i D))

/-- Use the actual orbit phase at each compared row. -/
def phaseAt (i : ℕ) (D : ℤ) : O :=
  if hD : W.admissible i D then (A i D hD).weights.phase (A i D hD).reference else 1

theorem phaseAt_eq (i : ℕ) (D : ℤ) (hD : W.admissible i D) :
    phaseAt s S A i D = (A i D hD).weights.phase (A i D hD).reference :=
  dite_eq_left hD

variable (contract : ∀ i (n : ℤ), (2 : O) ^ W.Mθ i ∣ (n : O) → (2 : ℤ) ^ W.Mθ i ∣ n)
  (ha : ∀ i D (hD : W.admissible i D),
    (2 : O) ^ W.Mθ i ∣ (A i D hD).weights.phase (A i D hD).reference * (W.aθ i D : O) -
      thetaCoeff (S i).visibility ((((S i).weights.m : ℤ) * D : ℤ) : ℚ))

/-- The phase and coefficient reading for the actual theta stages. -/
def thetaSide : ThetaSide W.toRCData O where
  aq _ := -1
  bq i := -((S i).ell : ℚ)
  S i := (S i).visibility
  ζ := phaseAt s S A
  phase_unit i D hD := by
    rw [phaseAt_eq s S A i D hD]
    exact (A i D hD).weights.phase_unit (A i D hD).reference
  coeff i D hD := by
    rw [phaseAt_eq s S A i D hD]
    simpa only [(S i).m_eq] using ha i D hD
  ring_two := contract

set_option maxHeartbeats 1000000 in
/-- The accepted odd wiring from the actual reference records. The existing
orbit calculation supplies hcore for the same map as the witness pin. -/
def toOddStagedInstanceOfReference
    (hL : MultiplierKillsNativeTorsion (Ecurve ℓ) I.f I.Lat I.κ W.hstar L)
    (hsign : AdmissibleOddSign W.toRCData) : OddStagedInstance W :=
  s.toOddStagedInstance hL hsign N.primeFactors.card (thetaSide s S A contract ha)
    (fun i D hD => by
      change ComparisonCore (S i).visibility (W.Mθ i) (-W.hstar) D N.primeFactors.card
        (lamOf W.Mθ L I.selG s.ev i D) (phaseAt s S A i D)
      rw [phaseAt_eq s S A i D hD]
      exact coreOfDatum (A i D hD) (contract i) (W.aθ i D) (ha i D hD))

end ZInQ.Manuscript.RC.StageKummer

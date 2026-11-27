import ZInQKernel.Contrib.OneProof.RC.StageKummer.Wiring
import ZInQKernel.Contrib.OneProof.RC.StageKummer.Transport
import ZInQKernel.Contrib.OneProof.RC.O7Actual.Family

/-! The reference reduction, tex 9265–9291. Both CM inputs are statements
about individual conjugates at the place used by the detector. -/

noncomputable section

open WeierstrassCurve TauCeti TauCeti.ClassFieldTheory
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.GenusOdd
open ZInQ.Manuscript.RC.PrintsArith ZInQ.Manuscript.RC.Stages
  ZInQ.Manuscript.RC.Visibility ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.WitnessSpec
open scoped WeierstrassCurve Classical

set_option linter.style.haveILetI false

namespace ZInQ.Manuscript.RC.StageKummer

open Eichler PMGeometry O7Actual O12StageVal Visibility.ThetaStage

/-- The Artin matching in the reference orbit, with the same datum character. -/
abbrev ArtinMatch {C : WeierstrassCurve ℤ}
    {f : CuspForm (CongruenceSubgroup.Gamma0 (CST.newformLevel (C⁄ℚ)) :
      Subgroup (GL (Fin 2) ℝ)) 2} {Lat : PeriodPair} {κ : ℂ} {hstar D : ℤ}
    (t : HeegnerDatum (C⁄ℚ) f Lat κ (D * hstar) 1 hstar)
    {O : Type} [CommRing O] {Cl : Type} (e : Cl ≃ DatumGalois t) (χF : Cl → O) : Prop :=
  letI := t.field; letI := t.nf; letI := t.nz
  ∀ c, χF c = ((chiSign t.χ
    ((ringClassArtinEquiv (CST.conductorOrder t.K 1)).symm (e c)) : ℤ) : O)

variable {ℓ : ℕ} {W : WData ℓ} {I : GenusOddInstance W} {L : ℕ} (s : Setup I L)
  (i : ℕ) [Fact (s.q.stage i).p.Prime]
  [(ReducedEquation (EcurveZ ℓ) (s.q.stage i).p).IsElliptic]

abbrev place :=
  letI := s.eE; letI := s.eA
  FrobeniusPlace.ofIsFrobAt (selectedFrobenius s.q i).property.1

abbrev detector :=
  letI := s.eE; letI := s.eA
  StageIdent.selectedEvaluationOn (EcurveZ ℓ) (EcurveZ_baseChange ℓ) rfl rfl s.dat s.w
    s.hQw s.q s.hσ s.b s.hb s.hstages.Mθ_eq i

omit [Fact (s.q.stage i).p.Prime] in
/-- The existing identification of the chosen detector with the evaluation
component of the family, on the entire quadratic residue point group. -/
theorem detector_lam :
    letI := s.eE; letI := s.eA
    HEq (PM.lam (detector s i))
      ((StageMap.actualForStages W s.dat s.w s.hQw s.q s.hσ s.embeddings
        s.b s.hstages.withStages_eq).eval i) :=
  letI := s.eE; letI := s.eA
  StageIdent.selectedEvaluationOn_lam (EcurveZ ℓ) (EcurveZ_baseChange ℓ) rfl rfl
    s.dat s.w s.hQw s.q s.hσ s.b s.hb s.hstages.Mθ_eq i s.embeddings

variable {D : ℤ} (t : HeegnerDatum (Ecurve ℓ) I.f I.Lat I.κ (D * W.hstar) 1 W.hstar)

abbrev chosenDatum := datumOnModel (EcurveZ_baseChange ℓ) t

abbrev chosenDatumPlace (hs : stageTest s.q i D) :
    DatumPlace (chosenDatum t) (place s i) :=
  letI := s.eE; letI := s.eA
  datumPlaceOn (EcurveZ_baseChange ℓ) rfl rfl s.dat s.w s.hQw s.q
    s.embeddings i t hs

abbrev goodAt :
    ¬ ((s.q.stage i).p : ℤ) ∣ (EcurveZ ℓ).Δ :=
  letI := s.eE; letI := s.eA
  stageGood (EcurveZ_baseChange ℓ) rfl rfl s.dat s.w s.hQw s.q i

abbrev reduceDatum (hs : stageTest s.q i D) :=
  datumReduction (chosenDatum t) (place s i) (chosenDatumPlace s i t hs)
    (goodAt s i)

set_option maxHeartbeats 600000 in
/-- The exact stage agreement used in the reference reduction, with the
detector of the skeleton stage and the same datum place. -/
theorem hev_at (hs : stageTest s.q i D) :
    evOnModel (EcurveZ_baseChange ℓ) s.ev i D (chosenDatum t) =
      datumComposite (chosenDatum t) (place s i) (chosenDatumPlace s i t hs)
        (goodAt s i) (detector s i) := by
  letI := s.eE; letI := s.eA
  have he := evActual_eq_comp (EcurveZ_baseChange ℓ) rfl rfl s.dat s.w s.hQw s.q s.hσ
    s.embeddings s.b s.hb s.hstages.Mθ_eq i (D := D) t hs
  dsimp +instances only [chosenDatum, place, goodAt, chosenDatumPlace, detector, Setup.ev] at he ⊢
  exact he

variable {a b : ℚ} {R : Order a b}
  {A : PMGeometry.Adelic (ell := (s.q.stage i).p)
    (N := CST.newformLevel ((EcurveZ ℓ)⁄ℚ)) R}
  {ap : ℕ → ℤ}
  (J : GeometricInput A (ResidueAt (place s i)) (ReducedEquation (EcurveZ ℓ) (s.q.stage i).p) ap)
  {O : Type} [CommRing O] {Cl : Type} [Fintype Cl]
  (e : Cl ≃ DatumGalois (chosenDatum t)) (z : Cl → ClassSet R) (χF : Cl → O)
  (hs : stageTest s.q i D)
  (r : Cl → J.Point)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 3200 in
/-- The reference reduction required by DatumAt.reduce. The specialization
premises use the same coarse model and the exact chosen place. -/
theorem reference_reduction
    (ht : I.selG D = some t)
    (hχF : ArtinMatch (chosenDatum t) e χF)
    (hCM : ∀ c, r c = (J.classes (z c)).val)
    (hπ : ∀ c, J.specialize (r c) = reduceDatum s i t hs (conjugate (chosenDatum t) (e c)))
    {u : ClassSet R → ℤ} (hu : PM.IsLift J.geometry (detector s i) L u) :
    (2 : O) ^ W.Mθ i ∣ ∑ c, χF c * (u (z c) : O) - (lamOf W.Mθ L I.selG s.ev i D : O) := by
  letI := Classical.decEq (DatumField (chosenDatum t))
  let cmInputs : InputsAtDatum A ap (reduceDatum s i t hs) (conjugate (chosenDatum t) ∘ e) z :=
    ⟨J, r, hCM, hπ⟩
  rw [← lamOf_onModel (EcurveZ_baseChange ℓ) W.Mθ L I.selG s.ev i D]
  exact lamOf_reduction_at (chosenDatum t) (place s i) (chosenDatumPlace s i t hs)
    (goodAt s i)
    W.Mθ i L (detector s i) (selectorOnModel (EcurveZ_baseChange ℓ) I.selG)
    (evOnModel (EcurveZ_baseChange ℓ) s.ev)
    (selectorOnModel_some (EcurveZ_baseChange ℓ) ht)
    (hev_at s i t hs)
    e z χF hχF cmInputs hu


omit [Fact (s.q.stage i).p.Prime] [(ReducedEquation (EcurveZ ℓ) (s.q.stage i).p).IsElliptic] in
/-- The actual Chebotarev congruence at precision at least two gives the
prime needed by the explicit level order. -/
theorem stage_mod_four : (s.q.stage i).p % 4 = 3 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hcast, _, _⟩ := (s.q.stage i).arithmetic
  exact Odd.mod_four_of_neg_one (by omega) hcast

section DatumAt

abbrev level (ℓ : ℕ) := CST.newformLevel ((EcurveZ ℓ)⁄ℚ)

variable {hN : 0 < level ℓ} {m : ℤ}
  {A' : PMGeometry.Adelic (ell := (s.q.stage i).p) (N := level ℓ)
    (Adelic.levelOrder (s.q.stage i).p (stage_mod_four s i) (level ℓ) hN)}
  (J' : GeometricInput A' (ResidueAt (place s i)) (ReducedEquation (EcurveZ ℓ) (s.q.stage i).p) ap)
  (F : PMLocal O (Adelic.levelOrder (s.q.stage i).p (stage_mod_four s i) (level ℓ) hN) (W.Mθ i) (level ℓ) (s.q.stage i).p)
  (hm : (F.m : ℤ) = m)

/-- Build the reference stage with the chosen detector and the least lifts
of its actual weights. Its geometry comes from the same coarse model. -/
def referenceStage : StageAt O (level ℓ) (W.Mθ i) hN m where
  ell := (s.q.stage i).p
  prime := inferInstance
  mod_four := stage_mod_four s i
  K := ResidueAt (place s i)
  field := inferInstance
  alg := inferInstance
  dec := inferInstance
  closed := inferInstance
  Ebar := ReducedEquation (EcurveZ ℓ) (s.q.stage i).p
  elliptic := inferInstance
  ap := ap
  G := J'.geometry
  d := detector s i
  L := L
  weights := F
  m_eq := hm
  u := PM.valLift J'.geometry (detector s i) L
  hu := PM.isLift_valLift J'.geometry (detector s i) L

variable (Q : IntegralSupport (referenceStage s i J' F hm) D)
  (orbits : OrbitFibers (referenceStage s i J' F hm).visibility
    (((F.m : ℤ) * D : ℤ) : ℚ) (level ℓ).primeFactors.card Q.classGroup)
  (weights : TorusWeights _ orbits)
  (moves : Normalizers J'.geometry (detector s i) L F
    (referenceStage s i J' F hm).u (referenceStage s i J' F hm).hu orbits)
  (ref : Orientations (level ℓ).primeFactors.card)
  (artin : Q.classGroup ≃ DatumGalois (chosenDatum t))
  (r' : Q.classGroup → J'.Point)
  (hCM : ∀ c, r' c = (J'.classes (zc orbits.param (ref, c))).val)
  (hπ : ∀ c, J'.specialize (r' c) = reduceDatum s i t hs (conjugate (chosenDatum t) (artin c)))

set_option maxHeartbeats 1600000 in
/-- Fill DatumAt.reduce on the constructed stage and the same selector's
lambda. The other record fields are the separate orbit data. -/
def datumAt
    (ht : I.selG D = some t) (hχF : ArtinMatch (chosenDatum t) artin weights.character) :
    DatumAt (referenceStage s i J' F hm) D (lamOf W.Mθ L I.selG s.ev i D) where
  support := Q
  orbits := orbits
  weights := weights
  moves := moves
  reference := ref
  reduce := by
    exact reference_reduction s i t J' artin (fun c => zc orbits.param (ref, c))
      weights.character hs r' ht hχF hCM hπ (referenceStage s i J' F hm).hu

end DatumAt

end ZInQ.Manuscript.RC.StageKummer

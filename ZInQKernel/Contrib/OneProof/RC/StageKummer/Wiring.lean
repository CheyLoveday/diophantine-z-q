import ZInQKernel.Contrib.OneProof.RC.StageKummer.Actual
import ZInQKernel.Contrib.OneProof.RC.Wiring.StageData

/-! Assemble the odd wiring with the actual stage map. The genus and
Appendix F data precede the choice of theta side (provenance (c)). -/

noncomputable section

open WeierstrassCurve TauCeti
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.GenusOdd
open ZInQ.Manuscript.RC.PrintsArith ZInQ.Manuscript.RC.Stages
  ZInQ.Manuscript.RC.Visibility ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.WitnessSpec
open scoped WeierstrassCurve Classical

namespace ZInQ.Manuscript.RC.StageKummer

/-- The data of the witness and detector prior to building the theta comparison.
In particular they do not require an old stage map or its witness pin. -/
structure Setup {ℓ : ℕ} {W : WData ℓ} (I : GenusOddInstance W) (L : ℕ) where
  [eE : (Ecurve ℓ).IsElliptic]
  Dw : ℤ
  hDw : W.prepared Dw
  dat : HeegnerDatum (Ecurve ℓ) I.f I.Lat I.κ (Dw * W.hstar) 1 W.hstar
  hdat : I.selG Dw = some dat
  w : ExactWitnessOn (Ecurve ℓ) rfl rfl dat L
  [eA : (qtwist (Ecurve ℓ) Dw).IsElliptic]
  Q : GeomPoint (qtwist (Ecurve ℓ) Dw)
  hQw : Q = rationalGeomPoint (qtwist (Ecurve ℓ) Dw) w.rational
  hQ : ∀ g : GalQ, Affine.Point.map (W' := qtwist (Ecurve ℓ) Dw) g.toAlgHom Q = Q
  d : DivisionTower (qtwist (Ecurve ℓ) Dw) Q
  F₀ : IntermediateField ℚ Qbar
  σ : GalQ
  hσ : tateRep (Ecurve ℓ) 2 (σ * σ) = 1
  a : ℕ
  b : TateMod (qtwist (Ecurve ℓ) Dw) 2 →ₗ[ℤ_[2]] ℤ_[2]
  hb : ∀ t, b (tateRep (qtwist (Ecurve ℓ) Dw) 2 σ t) = b t
  hvalue : b (d.cocycle hQ (σ * σ)) = 2 ^ (a + 1)
  B : Finset ℕ
  q : StageSequence (ActualAt (qtwist (Ecurve ℓ) Dw) (Ecurve ℓ) Q F₀ σ Dw W.hstar) (a + 1) B
  hstages : StagesFrom W q

namespace Setup

variable {ℓ : ℕ} {W : WData ℓ} {I : GenusOddInstance W} {L : ℕ} (s : Setup I L)

/-- A fixed realization of the nonwitness datum fields; the construction
of the place overrides its witness entry by the existing exact embedding. -/
abbrev embeddings : StageMap.DatumEmbeddings (Ecurve ℓ) I.f I.Lat I.κ W.hstar :=
  witnessEmbeddings s.w

/-- The one stage map consumed by the comparison and the witness. -/
abbrev ev : Visibility.StageKummer (Ecurve ℓ) I.f I.Lat I.κ W.hstar W.Mθ :=
  letI := s.eE; letI := s.eA
  evActual (EcurveZ_baseChange ℓ) rfl rfl s.dat s.w s.hQw s.q s.hσ
    s.embeddings s.b s.hstages.Mθ_eq

/-- Discharge the existing witness pin using the shared stage map. -/
theorem hev (i : ℕ) :
    letI := s.eE; letI := s.eA
    s.ev i s.Dw s.dat = actualStageMapOn (EcurveZ ℓ) (EcurveZ_baseChange ℓ) rfl rfl
      s.dat s.w s.hQw s.q s.hσ s.b s.hstages.Mθ_eq i s.Dw s.dat :=
  letI := s.eE; letI := s.eA
  evActual_witness (EcurveZ_baseChange ℓ) rfl rfl s.dat s.w s.hQw s.q s.hσ
    s.embeddings s.b s.hb s.hstages.Mθ_eq i

/-- An admissible row is on the moving split support of the actual stage. -/
theorem stageTest_of_admissible {i : ℕ} {D : ℤ} (hD : W.admissible i D) :
    letI := s.eE; letI := s.eA
    stageTest s.q i D :=
  letI := s.eE; letI := s.eA
  StageMap.admissible_stageTest W s.hstages.withStages_eq hD

variable (hL : MultiplierKillsNativeTorsion (Ecurve ℓ) I.f I.Lat I.κ W.hstar L)
  (hsign : AdmissibleOddSign W.toRCData) (ω : ℕ) {O : Type} [CommRing O]
  (T : ThetaSide W.toRCData O)
  (hcore : ∀ θ D, W.admissible θ D →
    ComparisonCore (T.S θ) (W.Mθ θ) (-W.hstar) D ω
      (lamOf W.Mθ L I.selG s.ev θ D) (T.ζ θ D))

/-- Build the accepted wiring record. The theta consumer is indexed by the
actual evaluation; it can no longer be filled using an arbitrary pinned map. -/
def toOddStagedInstance : OddStagedInstance W where
  toOddModels :=
    { toGenusOddInstance := I
      L := L
      hL := hL
      ev := s.ev
      hsign := hsign
      ω := ω
      O := O
      T := T
      hcore := hcore }
  eE := s.eE
  Dw := s.Dw
  hDw := s.hDw
  dat := s.dat
  hdat := s.hdat
  w := s.w
  eA := s.eA
  Q := s.Q
  hQw := s.hQw
  hQ := s.hQ
  d := s.d
  F₀ := s.F₀
  σ := s.σ
  hσ := s.hσ
  a := s.a
  b := s.b
  hvalue := s.hvalue
  B := s.B
  q := s.q
  hstages := s.hstages
  hev := s.hev

end Setup

end ZInQ.Manuscript.RC.StageKummer

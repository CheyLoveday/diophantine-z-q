import ZInQKernel.Contrib.OneProof.RC.StageKummer.Wiring
import ZInQKernel.Contrib.OneProof.RC.StageSelector.Selector

/-! Install the extended selector in the genus record and keep its index
consistent with the record. Reindexing the otherwise unchanged wiring
parameters is on-the-spot (c). -/

noncomputable section

open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd
open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.Stages

namespace ZInQ.Manuscript.RC.StageKummer

open StageSelector

variable {ℓ : ℕ} {W : WData ℓ} {I : GenusOddInstance W} {L : ℕ} (s : Setup I L)

include s in
theorem positiveLevel : 0 < newformLevel (Ecurve ℓ) := by
  by_contra! hN
  have h0 : newformLevel (Ecurve ℓ) = 0 := Nat.eq_zero_of_le_zero hN
  have hA : s.dat.A = 0 := by
    have h := s.dat.form.2.1
    simpa [h0] using h
  exact (ne_of_gt s.dat.form.1) hA

abbrev preparedGlue := preparedGlue_of_withStages s.hstages.withStages_eq

/-- The selector lane's only new datum input, at admissible nonwitness holes. -/
abbrev MissingParamValues : Prop :=
  ∀ D (h : ∃ θ, W.admissible θ D), D ≠ s.Dw → I.selG D = none →
    PreparedParamValue (Ecurve ℓ) I.f I.Lat I.κ (positiveLevel s) I.hgp
      (I.hprep D (preparedGlue s h.choose D h.choose_spec))

variable (h : MissingParamValues s)

abbrev extendedSelector := extendSelG I s.dat (preparedGlue s) h

/-- Every admissible stage has a selected row, including the witness. -/
theorem selected_of_admissible {i : ℕ} {D : ℤ} (hD : W.admissible i D) :
    ∃ t, extendedSelector s h D = some t :=
  exists_selected_of_admissible I s.dat (preparedGlue s) h s.hdat hD

/-- The genus record stores a global equation for jgen. Recompute jgen
when filling the selector's holes, leaving all stage fields fixed. -/
def withExtendedIndex : WData ℓ :=
  { W with jgen := jgenOf (Ecurve ℓ) I.f I.Lat I.κ W.hstar (extendedSelector s h) }

/-- At every prepared simple zero, the recomputed index equals the old one. -/
theorem extendedIndex_at_simpleZero {D : ℤ} (hp : W.prepared D)
    (hz : AnalyticRank (qtwist (Ecurve ℓ) D) 1) :
    (withExtendedIndex s h).jgen D = W.jgen D :=
  jgen_extendSelG_at_simpleZero I s.dat (preparedGlue s) h hp hz

/-- Preserve the genus inputs and all previously selected data. -/
def extendedGenus : GenusOddInstance (withExtendedIndex s h) :=
  { I with
    selG := extendedSelector s h
    hselG := fun D hp hz => by
      obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (I.hselG D hp hz)
      exact Option.isSome_iff_exists.mpr ⟨t, extendSelG_eq_some I s.dat (preparedGlue s) h ht⟩
    hjg := rfl }

/-- Keep the same sequence, row and witness when installing the selector. -/
def extendedSetup : Setup (extendedGenus s h) L :=
  { s with
    hdat := extendSelG_witness I s.dat (preparedGlue s) h s.hdat
    hstages := ⟨s.hstages.stages_eq, s.hstages.Mθ_eq, s.hstages.admissible_eq⟩ }

/-- Selector extension changes which entry is read, but the shared family
itself is the same homomorphism family. -/
theorem extendedSetup_ev : (extendedSetup s h).ev = s.ev := rfl

end ZInQ.Manuscript.RC.StageKummer

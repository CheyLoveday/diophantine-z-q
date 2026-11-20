import ZInQKernel.Contrib.OneProof.RC.PicardFibers.Assembly
import ZInQKernel.Contrib.OneProof.RC.TorusWeights.Actual

/-! The adelic frame read for the orbit of a specified representative.
This adapter is on-the-spot (c), for tex 9155–9179. -/

noncomputable section

namespace ZInQ.Manuscript.RC.O7Assemble

open Eichler Adelic O7Actual O7Orbits PicardFibers Visibility

set_option maxHeartbeats 400000 in
/-- A known adelic orbit has a presentation in the very same rational left
order representative read by the theta weights. The orbit equality is
separate from the rational frame change. -/
theorem framePresents {O : Type} [CommRing O] {N M : ℕ} {hN : 0 < N} {m D : ℤ}
    (s : StageAt O N M hN m) (H : SupportBridge s D)
    {x₀ α : B (-1) (-(s.ell : ℚ))} (hα : 2 * α - 1 = x₀) (hx : x₀.re = 0)
    (hn : nrd x₀ = index s D) (z : FiniteUnits (O7Orbits.ActualOrder s))
    (hz : AdelicAdmissible α z) (P : OrbitSet s.visibility (index s D))
    (hP : P = orbitFromRep s H hα hx hn ⟨z, hz⟩) :
    ∃ q : (B (-1) (-(s.ell : ℚ)))ˣ,
      (Eichler.representative P.1).val = (fromAdelic z).val.translate q ∧
      ∃ x : s.visibility.supp P.1 (index s D),
        x.val = q.val * x₀ * (↑q⁻¹ : B (-1) (-(s.ell : ℚ))) ∧ Quotient.mk _ x = P.2 := by
  subst P
  let q := (exists_frame z).choose
  let r := (exists_frame z).choose_spec.choose
  let hf := (exists_frame z).choose_spec.choose_spec
  refine ⟨q, ?_, supportFromFrame s H hα hx hn hz q r hf, rfl, rfl⟩
  change (Eichler.representative (adelicClass z)).val = (fromAdelic z).val.translate q
  rw [← fromAdelic_classRepresentative (adelicClass z)]
  exact (fromAdelic_translate_iff z (classRepresentative (adelicClass z)) q).mpr ⟨r, hf⟩

end ZInQ.Manuscript.RC.O7Assemble

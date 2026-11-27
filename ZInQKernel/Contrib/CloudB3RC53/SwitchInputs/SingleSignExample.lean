import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.SingleSign
import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.NonVacuitySingle3

/-!
# RC53 SwitchInputs: a terminating switching datum with a single-sign switch (`3 → 3 → 1`)

non-vacuity for the single-sign field of `SelmerModelSwitchData` (tex L5123–5136, L4976–5195): with
the dimension-three single-sign Selmer example `exQuadSingleStep3` (`NonVacuitySingle3.lean`, global
part `ℚ²`), `singleSignSwitchData` (`SingleSign.lean`) is a quadratic switching datum whose stage of
fiber dimension three carrying one sign switches with one sign to a stage of fiber dimension three
carrying both signs, which switches with mixed signs to a stage of fiber dimension one; regularity
holds at every stage. This removes the obstruction recorded in `NonVacuityModelQuad.lean` (the
dimension-two single-sign example cannot start a terminating chain).

Classification: PROVED (non-vacuity).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.SwitchInputs

open Module ZInQ.Contrib.CloudB3RC53.PairedFunctional

/-- **A terminating quadratic switching datum with a single-sign switch** (`3 → 3 → 1`). PROVED. -/
def exSingleSignSwitchData : SelmerModelSwitchData (k := ℚ) (RingHom.id ℚ) (RingHom.id ℚ) :=
  singleSignSwitchData exQuadSingleStep3 finrank_V3

/-- The example's chain: dimension three with one sign, dimension three with both signs, dimension
one. PROVED. -/
theorem exSingleSignSwitchData_chain :
    (exSingleSignSwitchData.stage .a).fiberDim (RingHom.id ℚ) = 3 ∧
      finrank ℚ ↥(signPart (exSingleSignSwitchData.σ .a) (-1 : ℚ)) = 0 ∧
      (exSingleSignSwitchData.stage .b).fiberDim (RingHom.id ℚ) = 3 ∧
      (0 < finrank ℚ ↥(signPart (exSingleSignSwitchData.σ .b) (1 : ℚ)) ∧
        0 < finrank ℚ ↥(signPart (exSingleSignSwitchData.σ .b) (-1 : ℚ))) ∧
      (exSingleSignSwitchData.stage .c).fiberDim (RingHom.id ℚ) = 1 :=
  singleSignSwitchData_chain exQuadSingleStep3 finrank_V3

/-- **Regularity from the example** (RC16's regularity at every stage). PROVED. -/
theorem exSingleSignSwitch_regular (S : Stage3) :
    ∃ a : ℚ, RingHom.id ℚ a = (exSingleSignSwitchData.stage S).u :=
  singleSignSwitch_regular exQuadSingleStep3 finrank_V3 S

end ZInQ.Contrib.CloudB3RC53.SwitchInputs

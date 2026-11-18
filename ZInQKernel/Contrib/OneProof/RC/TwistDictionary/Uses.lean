import ZInQKernel.Contrib.OneProof.RC.TwistDictionary.Dictionary
import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.Bridges

/-!
# Lane RC18-twist: lane RC8's curve forms without the GLUE `TwistDictionary`

Lane RC8 derives the curve forms of the analytic prints (Hoffstein–Luo, the twisted functional
equation, Bump–Friedberg–Hoffstein; App G tex 9995–10051 and tex 1984–1992) from the literal prints
over newforms, `ModularNewform`, and the two GLUEs `TwistDictionary` and `HasseConvergence`. With
`twistDictionary` (PROVED in `Dictionary.lean`) only `HasseConvergence` remains.

All results here are `PROVED`.
-/

namespace ZInQ.Manuscript.RC.TwistDictionary

open ZInQ.Manuscript.RC.PrintsAnalytic

/-- **Twisted newform L-functions continue `L(E^{(D)}, s)`** (PROVED): lane RC8's
`isLContinuation_qtwist` with `twistDictionary`. -/
theorem isLContinuation_qtwist' (hH : HasseConvergence) {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {N : ℕ} [NeZero N] {f : HeckeRing.GL2.Newform N 2} (hf : IsNewformOf E f) {D : ℤ}
    (hD : IsFundamentalDiscriminant D) (hDN : IsCoprime D (N : ℤ)) {σ₀ : ℝ} {F : ℂ → ℂ}
    (hF : IsEntireContinuation (twistCoeff (nfCoeff f) D) σ₀ F) :
    ZInQ.Contrib.CloudB3RC53.IsLContinuation (ZInQ.Contrib.CloudB3RC53.qtwist E D) F :=
  isLContinuation_qtwist twistDictionary hH hf hD hDN hF

/-- **Hoffstein–Luo for elliptic curves** (PROVED from the print, `ModularNewform` and
`HasseConvergence`). -/
theorem hoffsteinLuoCurve_of_print (hHL : HoffsteinLuoTheorem) (hM : ModularNewform)
    (hH : HasseConvergence) : HoffsteinLuoCurve :=
  hoffsteinLuoCurve_of hHL hM twistDictionary hH

/-- **The twisted functional equation for elliptic curves** (PROVED from the print,
`ModularNewform` and `HasseConvergence`). -/
theorem twistedRootNumberCurve_of_print (hTFE : TwistedFunctionalEquation) (hM : ModularNewform)
    (hH : HasseConvergence) : TwistedRootNumberCurve :=
  twistedRootNumberCurve_of hTFE hM twistDictionary hH

/-- **Bump–Friedberg–Hoffstein for elliptic curves** (PROVED from the print, `ModularNewform` and
`HasseConvergence`). -/
theorem bfhCurve_of_print (hB : BFHTheorem) (hM : ModularNewform) (hH : HasseConvergence) :
    BFHCurve :=
  bfhCurve_of hB hM twistDictionary hH

end ZInQ.Manuscript.RC.TwistDictionary

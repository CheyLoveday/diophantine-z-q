import ZInQKernel.Contrib.OneProof.RC.Even.KatoBridge
import ZInQKernel.Contrib.OneProof.RC.PrintsArith.Bundle
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.EvenLowerBound

/-!
# Lane RC22 (glue sweep), even share: (3.2) from Kato for the curves `E_ℓ` without the non-CM
# hypothesis

Lane RC11's `evenScalar32_of_kato` (`KatoBridge.lean`; tex 1884–1893, App E ¶7 tex 7206–7255)
derives (3.2) from lane RC9's PRINT `KatoZetaLeaf`, the ELLIOT step `AppEFromKato` and the
hypothesis `hCM : HasNoCM E`. For the curves of Theorem 5.3, `E = E_ℓ = Ecurve ℓ` (`ℓ > 0`), lane
RC9 PROVES `HasNoCM (curve ℓ)` from the GLUE `CMjInteger` (rational CM `j`-invariants are
integers; `j(E_ℓ) = 35152/9`, tex 1765–1767): `PrintsArith.curve_hasNoCM`. The bridges below
remove `hCM` (and the instance argument) for `E_ℓ`, and chain (3.2) into (E.9).

All results here are `PROVED`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.GlueSweep.Even

open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53 ZInQ.Manuscript.RC.PrintsArith

/-- **(3.2) for `E_ℓ` from Kato's printed theorems and Elliot's construction, non-CM discharged**
(Proposition `ex:sec7-even-scalar`, tex 1884–1893, 1832–1844; PROVED from lane RC9's PRINT
`KatoZetaLeaf`, lane RC9's GLUE `CMjInteger` and lane RC11's ELLIOT step `AppEFromKato`).
Consumer: lane RC11's `evenScalar32_of_kato` at `E = Ecurve ℓ` (hypothesis `hCM` removed; the
instance `[E.IsElliptic]` supplied by lane RC9's `ecurve_isElliptic`). Discharger: lane RC9's
`curve_hasNoCM` (`j(E_ℓ) = 35152/9 ∉ ℤ`). -/
theorem evenScalar32_of_kato_ecurve (hK : KatoZetaLeaf) (hcm : CMjInteger) {ℓ : ℕ} (hℓ : 0 < ℓ)
    {N : ℕ} (hN : N ≠ 0) {L : ZInQ.Manuscript.RC.Even.CentralNormalization (Ecurve ℓ)}
    (hE : @ZInQ.Manuscript.RC.Even.AppEFromKato (Ecurve ℓ) (ecurve_isElliptic hℓ) N L) :
    ZInQ.Manuscript.RC.Even.EvenScalar32 (Ecurve ℓ) N L :=
  @ZInQ.Manuscript.RC.Even.evenScalar32_of_kato hK (Ecurve ℓ) (ecurve_isElliptic hℓ)
    (curve_hasNoCM hcm (by exact_mod_cast hℓ.ne')) N hN L hE

/-- **(E.9) for `E_ℓ` from Kato's printed theorems and Elliot's construction** (tex 1884–1893
then 7777–7786; PROVED from lane RC9's PRINT `KatoZetaLeaf`, lane RC9's GLUE `CMjInteger`, lane
RC11's ELLIOT step `AppEFromKato`, the shared printed leaves `Prints` and lane RC8's GLUE
`HasseConvergence`): `evenScalar32_of_kato_ecurve` followed by
`evenLowerBound_of_evenScalar32_of_prints`. Consumers: lane RC11's `evenScalar32_of_kato` and
`evenLowerBound_of_evenScalar32` (hypotheses `hCM`, `hfwd`, `hcont` removed). -/
theorem evenLowerBound_of_kato_ecurve (hK : KatoZetaLeaf) (hcm : CMjInteger) (hP : Prints)
    (hH : ZInQ.Manuscript.RC.PrintsAnalytic.HasseConvergence) {ℓ : ℕ} (hℓ : 0 < ℓ)
    {N : ℕ} (hN : N ≠ 0) {L : ZInQ.Manuscript.RC.Even.CentralNormalization (Ecurve ℓ)}
    (hE : @ZInQ.Manuscript.RC.Even.AppEFromKato (Ecurve ℓ) (ecurve_isElliptic hℓ) N L) :
    ZInQ.Manuscript.RC.Even.EvenLowerBound (Ecurve ℓ) L :=
  @evenLowerBound_of_evenScalar32_of_prints hP hH (Ecurve ℓ) (ecurve_isElliptic hℓ) N L
    (evenScalar32_of_kato_ecurve hK hcm hℓ hN hE)

end ZInQ.Manuscript.RC.GlueSweep.Even

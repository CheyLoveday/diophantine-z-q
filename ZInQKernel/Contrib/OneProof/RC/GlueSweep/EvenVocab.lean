import ZInQKernel.Contrib.OneProof.RC.Skeleton.Setup
import ZInQKernel.Contrib.OneProof.RC.Even.EvenSource

/-!
# Lane RC22 (glue sweep), even share: lane RC11's vocabulary is lane RC0's

Lane RC0's skeleton and round-2 wiring (`Skeleton/Setup.lean`, `Wiring/EvenUpper.lean`:
`EvenUpperInputs`, the inputs of (3.3b) that restate lane RC11's (3.2) at corank-zero
constituents) and lane RC11 (`Even/EvenSource.lean`, `Even/Calibration.lean`) define the same
three objects under the same names in different namespaces:

* the central value `u(0)` (`RC.central` and `RC.Even.central`) — equal by definition;
* `ω(h)`, the number of distinct prime factors of `|h|` (`RC.omega` through Mathlib's
  `ArithmeticFunction.cardDistinctFactors`, `RC.Even.omega` through `Nat.primeFactors`);
* `s(h) = log₂ #Ш(E^{(h)}/ℚ)[2^∞]` (`RC.shaLength (qtwist E h)` and `RC.Even.shaLen E h`) — equal
  by definition;
* `u ∈ Λ[1/2]` inside `ℚ₂[[t]]` (`RC.InLamHalf`: `u = g/2^e` with `g` over `ℤ₂`;
  `RC.Even.InLamHalf`: `‖2^e uₙ‖ ≤ 1`) — equivalent.

These identifications (PROVED) let the two lanes' statements be compared verbatim.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.GlueSweep.Even

open ZInQ.Contrib.CloudB3RC53

/-- **The central value is the same function** (PROVED; tex 1945–1957): lane RC11's
`Even.central` and lane RC0's `central` are both `PowerSeries.coeff 0`. -/
theorem central_eq (u : PowerSeries ℚ_[2]) :
    ZInQ.Manuscript.RC.Even.central u = ZInQ.Manuscript.RC.central u :=
  rfl

/-- **`ω(h)` is the same function** (PROVED; tex 1838–1844, 7774–7775): lane RC11's
`Even.omega h` (the number of prime factors of `|h|`) equals lane RC0's `omega h = cardDistinctFactors |h|`. -/
theorem omega_eq (h : ℤ) : ZInQ.Manuscript.RC.Even.omega h = ZInQ.Manuscript.RC.omega h := by
  rw [ZInQ.Manuscript.RC.Even.omega, ZInQ.Manuscript.RC.omega,
    ArithmeticFunction.cardDistinctFactors_apply, ← Nat.toFinset_factors, List.card_toFinset]

/-- **`s(h)` is the same function** (PROVED; tex 1828–1830): lane RC11's `Even.shaLen E h` is
lane RC0's `shaLength` of the twist `E^{(h)} = qtwist E h`. -/
theorem shaLen_eq (E : WeierstrassCurve ℚ) (h : ℤ) :
    ZInQ.Manuscript.RC.Even.shaLen E h = ZInQ.Manuscript.RC.shaLength (qtwist E (h : ℚ)) :=
  rfl

/-- **`Λ[1/2]`-membership is the same predicate** (PROVED; tex 6841, 1945–1954): lane RC11's
`Even.InLamHalf u` (`‖2^e · coeff n u‖ ≤ 1` for all `n`) is lane RC0's `InLamHalf u`
(`coeff n u = g n / 2^e` with `g n ∈ ℤ₂`). -/
theorem inLamHalf_iff (u : PowerSeries ℚ_[2]) :
    ZInQ.Manuscript.RC.Even.InLamHalf u ↔ ZInQ.Manuscript.RC.InLamHalf u := by
  constructor
  · rintro ⟨e, he⟩
    refine ⟨e, fun n => ⟨(2 : ℚ_[2]) ^ e * PowerSeries.coeff n u, he n⟩, fun n => ?_⟩
    have h2 : (2 : ℚ_[2]) ^ e ≠ 0 := pow_ne_zero _ two_ne_zero
    show PowerSeries.coeff n u = (2 : ℚ_[2]) ^ e * PowerSeries.coeff n u / 2 ^ e
    field_simp
  · rintro ⟨e, g, hg⟩
    refine ⟨e, fun n => ?_⟩
    have h2 : (2 : ℚ_[2]) ^ e ≠ 0 := pow_ne_zero _ two_ne_zero
    have : (2 : ℚ_[2]) ^ e * PowerSeries.coeff n u = (g n : ℚ_[2]) := by
      rw [hg n]
      field_simp
    rw [this]
    exact PadicInt.norm_le_one (g n)

end ZInQ.Manuscript.RC.GlueSweep.Even

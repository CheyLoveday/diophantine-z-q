import ZInQKernel.OneProof.H.TailY

set_option linter.style.longLine false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ.HeightSplit

namespace GaRigidity

variable {k : Type} [Field k]

/-! ## §3. The local ring of `ℙ¹` at `∞`: `R = k[s]_(s)` with `s = 1/x`, its translations and its residue map -/

/-- The prime `(s) ⊆ k[s]`. -/
abbrev P0 (k : Type) [Field k] : Ideal (Polynomial k) := Ideal.span {Polynomial.X}

instance P0.isPrime : (P0 k).IsPrime :=
  (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr Polynomial.prime_X

/-- `R = k[s]_(s)`, a discrete valuation ring (the local ring of `ℙ¹` at `∞`, with `s = 1/x`). -/
abbrev Rl (k : Type) [Field k] : Type := Localization.AtPrime (P0 k)

/-- `K = Frac R`. -/
abbrev Kl (k : Type) [Field k] : Type := FractionRing (Rl k)

instance : IsDiscreteValuationRing (Rl k) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (Polynomial k)
    (by rw [Ne, Ideal.span_singleton_eq_bot]; exact Polynomial.X_ne_zero) (Rl k)

/-- The uniformizer `s ∈ R`. -/
abbrev sR (k : Type) [Field k] : Rl k := algebraMap (Polynomial k) (Rl k) Polynomial.X

theorem not_mem_P0 {y : Polynomial k} (hy : y ∈ (P0 k).primeCompl) : y.eval 0 ≠ 0 := by
  intro h
  apply hy
  show y ∈ P0 k
  rw [Ideal.mem_span_singleton, Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]
example : IsFractionRing (Rl k) (FractionRing (Rl k)) := @Localization.isLocalization (Rl k) _ (nonZeroDivisors (Rl k))
example : IsFractionRing (Localization.AtPrime (P0 k)) (FractionRing (Localization.AtPrime (P0 k))) := inferInstance
example (R : Type) [CommRing R] : IsFractionRing R (FractionRing R) := inferInstance
end GaRigidity

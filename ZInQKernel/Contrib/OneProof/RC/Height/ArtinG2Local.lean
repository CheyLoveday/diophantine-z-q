import ZInQKernel.Contrib.OneProof.RC.Height.ArtinG2
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.ArtinLocal
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.LocalFinal

/-!
# Lane RC27 (item 7): RC19's G2 from the local form of the Artin factorization

The shared top layer reduces its GLUE `GenusOdd.ArtinFactorization` (tex 2432) to local
statements: `GenusOdd.artinFactorization_of_local : HasseConvergence → GoodReductionOffLevel →
LocalFactorK → ArtinFactorization` (PROVED there; `HasseConvergence` is lane RC8's GLUE, Hasse's
bound; `GoodReductionOffLevel` and `LocalFactorK` are GLUE of the shared top layer). Composed with
`lFactorizationConductorOne_of_artin` (`ArtinG2.lean`), RC19's G2 (tex 5736) follows from these
three local GLUE statements. The shared top layer further proves `GoodReductionOffLevel` from lane
RC8's printed leaf `ModularNewform` (`GenusOdd.artinFactorization_of_newform : HasseConvergence →
ModularNewform → LocalFactorInert → ArtinFactorization`), which gives
`lFactorizationConductorOne_of_newform`.

No other file imports this one; it only records the composition. Every theorem in this file is
PROVED.
-/

noncomputable section

open NumberField

namespace ZInQ.Manuscript.RC.Height

open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST

/-- **RC19's G2 from the local GLUE of the Artin factorization** (tex 5736 with tex 2599, 2720;
tex 2432). PROVED: `lFactorizationConductorOne_of_artin` applied to the shared top layer's
`GenusOdd.artinFactorization_of_local hH hG hL`. Hypotheses on `K` as in
`lFactorizationConductorOne_of_artin` (non-vacuity: `artinG2_field_hypotheses_nonvacuous`). -/
theorem lFactorizationConductorOne_of_local
    (hH : ZInQ.Manuscript.RC.PrintsAnalytic.HasseConvergence)
    (hG : GenusOdd.GoodReductionOffLevel) (hL : GenusOdd.LocalFactorK)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (K : Type) [Field K] [NumberField K]
    (hK2 : Module.finrank ℚ K = 2) (hKc : IsTotallyComplex K) (h2 : SplitsIn K 2)
    (hsplit : ∀ p : ℕ, p.Prime → p ∣ newformLevel E → SplitsIn K p)
    {k : ℚ} {t : K} (ht : t ∉ (algebraMap ℚ K).range) (htk : t ^ 2 = algebraMap ℚ K k) :
    LFactorizationConductorOne E K k :=
  lFactorizationConductorOne_of_artin (GenusOdd.artinFactorization_of_local hH hG hL) E K hK2 hKc
    h2 hsplit ht htk

/-- **RC19's G2 from `HasseConvergence`, `ModularNewform` and `LocalFactorInert`** (tex 5736 with
tex 2599, 2720; tex 2432). PROVED: `lFactorizationConductorOne_of_artin` applied to the shared top
layer's `GenusOdd.artinFactorization_of_newform hH hMN hI` (`HasseConvergence`: lane RC8's GLUE,
Hasse's bound; `ModularNewform`: lane RC8's PRINT (BCDT); `LocalFactorInert`: GLUE of the shared top
layer, the Frobenius characteristic polynomial at inert primes). Hypotheses on `K` as in
`lFactorizationConductorOne_of_artin` (non-vacuity: `artinG2_field_hypotheses_nonvacuous`). -/
theorem lFactorizationConductorOne_of_newform
    (hH : ZInQ.Manuscript.RC.PrintsAnalytic.HasseConvergence)
    (hMN : ZInQ.Manuscript.RC.PrintsAnalytic.ModularNewform) (hI : GenusOdd.LocalFactorInert)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (K : Type) [Field K] [NumberField K]
    (hK2 : Module.finrank ℚ K = 2) (hKc : IsTotallyComplex K) (h2 : SplitsIn K 2)
    (hsplit : ∀ p : ℕ, p.Prime → p ∣ newformLevel E → SplitsIn K p)
    {k : ℚ} {t : K} (ht : t ∉ (algebraMap ℚ K).range) (htk : t ^ 2 = algebraMap ℚ K k) :
    LFactorizationConductorOne E K k :=
  lFactorizationConductorOne_of_artin (GenusOdd.artinFactorization_of_newform hH hMN hI) E K hK2
    hKc h2 hsplit ht htk

end ZInQ.Manuscript.RC.Height

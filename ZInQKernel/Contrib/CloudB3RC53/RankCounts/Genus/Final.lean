import ZInQKernel.Contrib.CloudB3RC53.RankCounts.Genus.Count
import ZInQKernel.Contrib.CloudB3RC53.RankCounts.Genus.Ambiguous
import ZInQKernel.Contrib.CloudB3RC53.RankCounts.Genus.InvariantRep
import ZInQKernel.Contrib.CloudB3RC53.RankCounts.Genus.Trichotomy
import ZInQKernel.Contrib.CloudB3RC53.RankCounts.Genus.Relation

/-!
# Elliot's genus bound (tex 4494–4517), fully assembled

`genus_bound`: for an imaginary quadratic field `K = ℚ(√k)` and any set `S` of primes of `K`,
`dim_{𝔽₂} Cl(𝒪_{K,S})[2] + 1 ≤ r`, `r` the number of rational primes ramified in `K` — the
inequality `dim Cl(𝒪_{K,S_T})[2] ≤ r − 1` of (5.1b). The 2-rank is Tau Ceti's `twoRank`.
Stages: trichotomy and inversion (`Trichotomy`), invariant representatives with Hilbert 90
(`InvariantRep`), ambiguous ideals (`Ambiguous`), the relation from `√d` (`Relation`), and the
count with the `S`-class quotient (`Count`). Kinds: PROVED.
-/

noncomputable section

open NumberField

namespace ZInQ.Contrib.CloudB3RC53.RankCounts.Genus

/-- **Elliot's genus bound** (tex 4494–4517). PROVED. -/
def GenusBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (k : ℤ) (α : 𝓞 K), IsQuadraticRadicand K k α →
    IsTotallyComplex K → ∀ S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)),
    TauCeti.twoRank (ClassGroup (S.integer K)) + 1 ≤ (ramifiedPrimes K k).card

theorem genusBound_proof : GenusBound := by
  intro K _ _ k α hα hTC S
  have hK2 := hα.1
  exact genus_bound_of K hK2 (invariantRep_of hK2 hTC (mulConjRational_proof hK2))
    (ambiguous_of hK2 (primeTrichotomy_proof hK2)) (ramRelation_of hK2 hTC (primeTrichotomy_proof hK2))
    hα S

end ZInQ.Contrib.CloudB3RC53.RankCounts.Genus

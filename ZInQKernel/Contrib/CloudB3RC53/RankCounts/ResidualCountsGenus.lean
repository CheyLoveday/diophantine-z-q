import ZInQKernel.Contrib.CloudB3RC53.RankCounts.ResidualCountsFull
import ZInQKernel.Contrib.CloudB3RC53.RankCounts.Genus.Final

/-!
# RankCounts: RC6's `ResidualRankCounts` with Elliot's genus bound proved

Manuscript `diophantine_zq.tex`, tex 4453–4648, with the genus inequality (5.1b), tex 4494–4517.
`residualRankCounts_genus` is `residualRankCounts_full` with `clDim := dim Cl(𝒪_{K,S_T})[2]`
(Tau Ceti's `twoRank` of the genuine `S_T`-class group) and RC6's field `genus` PROVED by
`Genus.genusBound_proof`. The remaining global input is `kummer` (Kummer theory and the `S`-unit
theorem for `G_{K,S_T}`, textbook, GLUE), now with the genuine `clDim`. Kinds: PROVED from the
named inputs.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.RankCounts

open NumberField IsDedekindDomain ZInQ.Manuscript.RC.Limits ZInQ.Contrib.CloudB3RC53.PairedFunctional

variable (K : Type) [Field K] [NumberField K]

/-- `dim_{𝔽₂} Cl(𝒪_{K,S_T})[2]` for `S_T` the primes above `T = primeSetT N r D Ram` (tex 4487). -/
abbrev clDimST (k : ℤ) (N r : ℕ) (D : Finset ℕ) : ℕ :=
  TauCeti.twoRank (ClassGroup ((primesAboveSet K (primeSetT N r D (ramifiedPrimes K k))).integer K))

open Classical in
/-- **RC6's `ResidualRankCounts` with the genus bound proved** (tex 4453–4648, 4494–4517). -/
def residualRankCounts_genus (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (k : ℤ) (α : 𝓞 K) (hα : IsQuadraticRadicand K k α)
    (hK : IsTotallyComplex K) (N : ℕ) (hN : N ≠ 0) (A : ℕ) (hA : k.natAbs.primeFactors.card ≤ A)
    (r : ℕ) (hr : r.Prime) (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime)
    (kummer : h1F2 K (primesAboveSet K (primeSetT N r D (ramifiedPrimes K k))) =
      (1 + ∑ p ∈ primeSetT N r D (ramifiedPrimes K k), nPlaces K p) + clDimST K k N r D)
    (cond : Ideal (𝓞 K) → LocalCondition) (condDim : Ideal (𝓞 K) → ℕ)
    (hcond : ∀ p ∈ chargedPrimes N r D, ∀ w ∈ placesList K cond condDim p,
      w.condDim = w.cond.dim w.deg)
    (archTot : ℕ) (arch_le : archTot ≤ 4)
    {S : Type} [CommRing S] [StrongRankCondition S] (Dsel : SelData S)
    [∀ n, Module.Free S (Dsel.G.X n)] [∀ n, Module.Finite S (Dsel.G.X n)]
    [∀ n, Module.Free S (Dsel.U.X n)] [∀ n, Module.Finite S (Dsel.U.X n)]
    [∀ n, Module.Free S (Dsel.L.X n)] [∀ n, Module.Finite S (Dsel.L.X n)]
    (s : Finset ℤ) (rankTot : ℕ)
    (hrank : rankTot = ∑ n ∈ s, Module.finrank S ((selCx Dsel).X n))
    (hG : ∑ n ∈ s, Module.finrank S (Dsel.G.X n) ≤
      hW K (primesAboveSet K (chargedPrimes N r D)) 0 +
        hW K (primesAboveSet K (chargedPrimes N r D)) 1 +
        hW K (primesAboveSet K (chargedPrimes N r D)) 2)
    (hL : ∑ n ∈ s, Module.finrank S (Dsel.U.X n) + ∑ n ∈ s, Module.finrank S (Dsel.L.X (n - 1)) ≤
      ∑ p ∈ chargedPrimes N r D, ((placesList K cond condDim p).map PlaceData.cost).sum + archTot)
    (genericRank : ℕ) (transfer : genericRank ≤ rankTot) : ResidualRankCounts :=
  residualRankCounts_full K h410 h51 h28 h23 k α hα hK N hN A hA r hr D hD (clDimST K k N r D)
    (Genus.genusBound_proof K k α hα hK _) kummer cond condDim hcond archTot arch_le Dsel s rankTot
    hrank hG hL genericRank transfer

end ZInQ.Contrib.CloudB3RC53.RankCounts

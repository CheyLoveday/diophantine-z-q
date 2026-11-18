import ZInQKernel.Contrib.CloudB3RC53.RankCounts.ResidualCounts

/-!
# Lane RC22 (glue sweep, limits): the counting steps of (5.1) for the genuine objects

Manuscript tex 4466–4591, proof of Lemma `ex:limits-residual-bound`. Lane RC6
(`RC/Limits/ResidualBound.lean`) proves the arithmetic of (5.1a), (5.1b), the global estimate (both
routes) and the archimedean allowance from numbers, each step taking its cohomological or
arithmetic inputs as explicit hypotheses (GLUE or PRINT). The tree now proves several of them for
the genuine objects (`CloudB3RC53/RankCounts/`: `QuadraticPlaces`, `GlobalPrints`, `GlobalH1`,
`Inflation`, `ResidualCounts`); they are used there only inside the constructor of RC6's
`ResidualRankCounts`. This file states RC6's individual step theorems with those hypotheses
removed. Every theorem here is PROVED from the remaining inputs listed in its docstring.
-/

namespace ZInQ.Manuscript.RC.GlueSweep.Lim

open NumberField IsDedekindDomain ZInQ.Manuscript.RC.Limits ZInQ.Contrib.CloudB3RC53
  ZInQ.Contrib.CloudB3RC53.RankCounts

/-- **(5.1a) for the genuine ramified primes**, tex 4466–4474: for `K = ℚ(√k)` (`hα`) and any
finite set `Ram` of rational primes ramified in `K`, `|T| ≤ ω(2N) + A + 1 + j`. PROVED, from no
remaining input (RC6's GLUE `hRam : Ram ⊆ primes(k) ∪ {2}` is discharged).

Consumer: RC6's `card_primeSetT_le` (hypothesis `hRam`, tex 4470); discharger: the tree's
`RankCounts.mem_primeFactors_of_isRamifiedPrime` (`QuadraticRamifiedDvdTwoK`). -/
theorem card_primeSetT_le_lim (K : Type) [Field K] [NumberField K] (k : ℤ) (α : 𝓞 K)
    (hα : IsQuadraticRadicand K k α) (N r A : ℕ) (D Ram : Finset ℕ) (hN : N ≠ 0)
    (hRam : ∀ p ∈ Ram, IsRamifiedPrime K p) (hk : k.natAbs.primeFactors.card ≤ A) :
    (primeSetT N r D Ram).card ≤ (2 * N).primeFactors.card + A + 1 + D.card :=
  card_primeSetT_le N r A k D Ram hN
    (fun p hp => mem_primeFactors_of_isRamifiedPrime k α hα (hRam p hp)) hk

/-- **The place count in (5.1b) for the genuine places**, tex 4494, 4516–4517: for a quadratic
field `K`, `T` a finite set of naturals and `Ram ⊆ T` primes ramified in `K`,
`|S_T| + r ≤ 2s` with `|S_T| = ∑_{p ∈ T} #(primes of K above p)`. PROVED, from no remaining input
(RC6's GLUE hypotheses `h2` — at most two places — and `h1` — one place over a ramified prime — are
discharged).

Consumer: RC6's `card_places_add_ram_le` (hypotheses `h2`, `h1`); dischargers: the tree's
`RankCounts.nPlaces_le_two_of_finrank`, `RankCounts.nPlaces_eq_one_of_isRamifiedPrime`. -/
theorem card_places_add_ram_le_lim (K : Type) [Field K] [NumberField K]
    (hK2 : Module.finrank ℚ K = 2) (T Ram : Finset ℕ) (hRamT : Ram ⊆ T)
    (hRam : ∀ p ∈ Ram, IsRamifiedPrime K p) :
    (∑ p ∈ T, nPlaces K p) + Ram.card ≤ 2 * T.card :=
  card_places_add_ram_le T Ram (nPlaces K) hRamT (fun p _ => nPlaces_le_two_of_finrank hK2 p)
    (fun _ hp => nPlaces_eq_one_of_isRamifiedPrime hK2 (hRam _ hp))

/-- **The global estimate at the residue field, genus route, for the genuine `G_{K,S₀}`**
(tex 4478–4533): with `hⁱ = dim_{𝔽₂} Hⁱ(G_{K,S₀}, 𝔽₂²)` (trivial action), `h² = h¹ − 4`, `h¹ ≤ 4s`,
`h⁰ + h¹ + h² + 2 ≤ 8s` and `h⁰ + h¹ + h² ≤ 8s + 2`, `s = |T|`. PROVED, from the PRINT leaves
`MilneADT_I_4_10_totallyComplex`, `MilneADT_I_5_1_totallyComplex` (Milne ADT I.4.10(c), I.5.1, as
stated in the tree) and the two remaining inputs of RC6's `global_estimate`: `kummer` (`hKummer`,
tex 4482–4492, GLUE: Kummer theory and the `S`-unit theorem, for the genuine `h¹(G_{K,S_T}, 𝔽₂)`)
and `genus` (`hCl`, tex 4494–4517, ELLIOT's genus argument). The hypotheses `hPlaces`, `hInf`,
`hW1`, `hW0`, `hEuler` of RC6's `global_estimate` are discharged. Here `K = ℚ(√k)` is imaginary
quadratic, `Ram ⊆ T` are ramified primes, `S₀ ⊆ S_T` are finite and `S₀` contains the primes above `2`.

Consumers: RC6's `global_estimate`, `GlobalCountsGenus.total_le`; dischargers: the tree's
`RankCounts.globalCountsGenus_of` (fields `nPlaces_le_two`, `nPlaces_ram`, `h0_eq`, `h1_eq`,
`euler`), `RankCounts.rc6InflationOfPrint_proof` (`inflation`). -/
theorem global_estimate_lim (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (K : Type) [Field K] [NumberField K] (k : ℤ) (α : 𝓞 K)
    (hα : IsQuadraticRadicand K k α) (hK : IsTotallyComplex K) (T Ram : Finset ℕ)
    (hRamT : Ram ⊆ T) (hRam : ∀ p ∈ Ram, IsRamifiedPrime K p)
    (S₀ ST : Set (HeightOneSpectrum (𝓞 K))) (hS₀ : S₀.Finite)
    (hS₀2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀) (hsub : S₀ ⊆ ST)
    (hST : ST.Finite) (clDim : ℕ) (genus : clDim + 1 ≤ Ram.card)
    (kummer : h1F2 K ST = (1 + ∑ p ∈ T, nPlaces K p) + clDim) :
    ((hW K S₀ 2 : ℤ) = hW K S₀ 1 - 4) ∧ hW K S₀ 1 ≤ 4 * T.card ∧
      hW K S₀ 0 + hW K S₀ 1 + hW K S₀ 2 + 2 ≤ 8 * T.card ∧
      hW K S₀ 0 + hW K S₀ 1 + hW K S₀ 2 ≤ 8 * T.card + 2 := by
  let G := globalCountsGenus_of K h410 h51 k α hα hK T Ram hRamT hRam S₀ ST hS₀ hS₀2 clDim genus
    kummer (rc6InflationOfPrint_proof h51 K hK S₀ ST hsub hST (fun v hv => hsub (hS₀2 v hv)))
  exact global_estimate T.card Ram.card _ G.clDim G.h1ST G.h1S0F2 G.h0 G.h1 G.h2 G.kummer
    (card_places_add_ram_le T Ram G.nPlaces G.ram_sub_T G.nPlaces_le_two G.nPlaces_ram)
    G.genus G.inflation G.h1_eq G.h0_eq G.euler

/-- **The weaker global estimate (generator route) for the genuine `G_{K,S₀}`** (tex 4534–4542):
`h¹(G_{K,S₀}, 𝔽₂²) ≤ 4s + 2` and `h⁰ + h¹ + h² ≤ 8s + 2`. PROVED, from the PRINT leaves Milne ADT
I.4.10/I.5.1 (tree) and the three remaining GLUE inputs of RC6's `global_estimate_weak`, which have no
prover in the tree (no generator counts of pro-2 Galois groups in Lean): `hGenQ` (`s + 1`
generators over `ℚ`), `hSchreier` (Schreier's index formula), `hQuot` (`h¹(G_{K,S₀}, 𝔽₂)` is at most
the number of generators). The hypotheses `hW1`, `hW0`, `hEuler` are discharged.

Consumers: RC6's `global_estimate_weak`, `GlobalCountsSchreier.total_le`; dischargers: the tree's
`RankCounts.globalCountsImagQuad_proof`, `RankCounts.h1_eq_two_mul`. -/
theorem global_estimate_weak_lim (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (K : Type) [Field K] [NumberField K]
    (hK2 : Module.finrank ℚ K = 2) (hK : IsTotallyComplex K)
    (S₀ : Set (HeightOneSpectrum (𝓞 K))) (hS₀ : S₀.Finite)
    (hS₀2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (s dQ dK : ℕ) (hGenQ : dQ = s + 1) (hSchreier : dK ≤ 2 * (dQ - 1) + 1)
    (hQuot : h1F2 K S₀ ≤ dK) :
    hW K S₀ 1 ≤ 4 * s + 2 ∧ hW K S₀ 0 + hW K S₀ 1 + hW K S₀ 2 ≤ 8 * s + 2 := by
  have hc := globalCountsImagQuad_proof h410 h51 K hK2 hK S₀ hS₀ hS₀2 (ZMod 2 × ZMod 2)
    inferInstance inferInstance finrank_zmod2_sq
  exact global_estimate_weak s dQ dK (h1F2 K S₀) (hW K S₀ 0) (hW K S₀ 1) (hW K S₀ 2) hGenQ
    hSchreier hQuot (h1_eq_two_mul (G := GaloisGroupS K S₀)) hc.1 hc.2.1

end ZInQ.Manuscript.RC.GlueSweep.Lim

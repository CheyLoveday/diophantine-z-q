import ZInQKernel.Contrib.CloudB3RC53.Mattuck.NonVacuity
import ZInQKernel.Contrib.CloudB3RC53.RankCounts.ResidualCountsKummer
import ZInQKernel.Contrib.OneProof.RC.Wiring.UniformSwitchResidual

/-!
# Mattuck, part 6: RC6's residual counts with the `(5.1)` table discharged

Manuscript `diophantine_zq.tex`, Lemma `ex:limits-residual-bound`, tex 4453–4648: the table of local
condition dimensions (tex 4544–4573) and "the derivative primes are odd and inert" (tex
4579–4580).

RC0's wiring `residualRankCounts_genusArch` (`RC/Wiring/UniformSwitchResidual.lean`) takes the
inputs `kummer` (GLUE) and `hcond` (the ELLIOT table). Here:

* `kummer` is batch 3's PROVED `kummer_field`;
* `hcond` is PROVED (`hcond_of_mattuck_all`) for the genuine condition dimensions with the old
  Kummer dimension computed by Mattuck at every place (odd places: `Mattuck/Odd`; places above `2`:
  `Mattuck/Two`), given
  - full rational `2`-torsion of the local integral models at the old-Kummer places (tex
    4479–4480, "`E^{(h)}[2]` is rational"; non-vacuity `exists_curve_card_twoTorsion_eq_four`), and
  - the derivative primes odd (tex 4579–4580) with the relaxed derivative condition used only at
    places above derivative primes: these give RC6's `hrel` (`hrel_of_odd`).

**`residualRankCounts_mattuck`**: `ResidualRankCounts` with only the Selmer-cone rank bounds `hG`,
`hL`, the support-change `transfer`, the condition assignment and the local models as inputs (and
the PRINT leaves Milne ADT I.4.10, I.5.1, I.2.8, I.2.3).

**Classification.** PROVED (from the inputs listed).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.Mattuck

open NumberField IsDedekindDomain ZInQ.Manuscript.RC.Limits ZInQ.Contrib.CloudB3RC53.RankCounts
  ZInQ.Contrib.CloudB3RC53.PairedFunctional

variable (K : Type) [Field K] [NumberField K]

/-- **RC6's `hrel` from "the derivative primes are odd"** (tex 4579–4580): if the relaxed
derivative condition is used only at places above primes of `D`, and the primes of `D` are odd,
then it is used only above odd primes. PROVED. -/
theorem hrel_of_odd (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime) (hDodd : ∀ p ∈ D, p ≠ 2)
    (cond : Ideal (𝓞 K) → LocalCondition)
    (hcondD : ∀ P : Ideal (𝓞 K), cond P = .derivRelaxed → ∃ q ∈ D, P ∈ primesAbove K q) :
    ∀ (p : ℕ), p.Prime → ∀ P ∈ primesAbove K p, cond P = .derivRelaxed → p ≠ 2 := by
  intro p hp P hP hc
  obtain ⟨q, hqD, hPq⟩ := hcondD P hc
  have hne : P ≠ ⊥ := ne_bot_of_mem_primesAbove K hp.ne_zero hP
  have hpP : ((p : ℤ) : 𝓞 K) ∈ P := (natCast_mem_asIdeal_iff K hp ⟨P, hP.1, hne⟩).mpr hP
  have hqP : ((q : ℤ) : 𝓞 K) ∈ P := (natCast_mem_asIdeal_iff K (hD q hqD) ⟨P, hP.1, hne⟩).mpr hPq
  have hpq : p = q := Genus.prime_eq_of_mem hP.1.ne_top hp (hD q hqD) hpP hqP
  rw [hpq]
  exact hDodd q hqD

variable (Ew : ∀ w : HeightOneSpectrum (𝓞 K), WeierstrassCurve (w.adicCompletionIntegers K))
  [hEw : ∀ w, ((Ew w).baseChange (w.adicCompletion K)).IsElliptic]

open Classical in
/-- **RC6's `ResidualRankCounts` with `kummer` and the `(5.1)` table discharged** (tex 4453–4648):
RC0's `residualRankCounts_genusArch` with `kummer := kummer_field` and
`hcond := hcond_of_mattuck_all` at the genuine condition dimensions
`condDimFun cond (kummerDimOfCurves Ew (kd2OfCurves Ew))` (Mattuck at every place). Remaining
inputs: the condition assignment `cond` (relaxed derivative conditions only above the odd
derivative primes `D`), the local integral models `Ew` with full rational `2`-torsion at the
old-Kummer places, the Selmer-cone rank bounds `hG`, `hL`, and `transfer`. PROVED. -/
def residualRankCounts_mattuck (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (k : ℤ) (α : 𝓞 K) (hα : IsQuadraticRadicand K k α)
    (hK : IsTotallyComplex K) (N : ℕ) (hN : N ≠ 0) (A : ℕ) (hA : k.natAbs.primeFactors.card ≤ A)
    (r : ℕ) (hr : r.Prime) (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime) (hDodd : ∀ p ∈ D, p ≠ 2)
    (cond : Ideal (𝓞 K) → LocalCondition)
    (hcondD : ∀ P : Ideal (𝓞 K), cond P = .derivRelaxed → ∃ q ∈ D, P ∈ primesAbove K q)
    (hfull : ∀ w : HeightOneSpectrum (𝓞 K), cond w.asIdeal = .oldKummer →
      Nat.card (Submodule.torsionBy ℤ ((Ew w).baseChange (w.adicCompletion K)).toAffine.Point 2) =
        4)
    (w : InfinitePlace K) (hw : w.IsComplex)
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
      ∑ p ∈ chargedPrimes N r D, ((placesList K cond
        (condDimFun K cond (kummerDimOfCurves K Ew (kd2OfCurves K Ew))) p).map
          PlaceData.cost).sum + archTotal K w)
    (genericRank : ℕ) (transfer : genericRank ≤ rankTot) : ResidualRankCounts :=
  ZInQ.Manuscript.RC.Wiring.residualRankCounts_genusArch K h410 h51 h28 h23 k α hα hK N hN A hA
    r hr D hD (kummer_field K hα hK hN hr hD) cond
    (condDimFun K cond (kummerDimOfCurves K Ew (kd2OfCurves K Ew)))
    (fun p _ v hv => hcond_of_mattuck_all K Ew h28 h23 cond (hrel_of_odd K D hD hDodd cond hcondD)
      hfull p v hv)
    w hw Dsel s rankTot hrank hG hL genericRank transfer

end ZInQ.Contrib.CloudB3RC53.Mattuck

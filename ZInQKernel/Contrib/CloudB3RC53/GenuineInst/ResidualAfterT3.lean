import ZInQKernel.Contrib.CloudB3RC53.GenuineInst.ResidualAfterT2
import ZInQKernel.Contrib.CloudB3RC53.ContBridge.Discrete

/-!
# Genuine instantiations, part 24: the degree-`3` identification against the genuine `genH`

Manuscript `diophantine_zq.tex`, Lemma `ex:limits-residual-bound`, tex 4521–4531 (`H^{>2} = 0`).

Part 22's `globalDegreeThreeVanishes_of_milne` / `residualRankCounts_afterT''` stated the degree-`3`
identification `eG3` against Mathlib's continuous `H³(G_{K,S₀}, W)`, because the comparison
`genHEquiv` of the genuine continuous cochains with Mathlib's continuous cohomology was available
only in degrees `≤ 2`. The ContBridge comparison `ContBridge.contCohomologyLinearEquiv` holds in
**every** degree (the peer's witness uses it at its instance as `allGenHEquiv`); here:

* `genHEquivAll K S₀ n`: `genH K S₀ n ≃ Hⁿ_cont(G_{K,S₀}, W)` (Mathlib) for all `n`;
* `globalDegreeThreeVanishes_of_milne_genH`: `GlobalDegreeThreeVanishes Dsel` from Milne ADT
  I.4.10 and an identification `eG3 : Dsel.G.X 3 ≃ genH K S₀ 3` — the same kind as `eG` in degrees
  `0..2`, against the genuine object;
* `residualRankCounts_afterT'''`: `residualRankCounts_afterT'` with that `eG3` in place of the named
  GLUE.

This removes the limitation recorded in part 22 (the missing degree-`3` genuine-to-Mathlib
comparison).

**Classification.** PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.GenuineInst

open NumberField IsDedekindDomain CategoryTheory ZInQ.Manuscript.RC.Limits
  ZInQ.Contrib.CloudB3RC53.RankCounts ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Manuscript.RC.SelmerComplex ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.Mattuck

/-- **The genuine global cohomology is Mathlib's continuous cohomology in every degree**:
`genH K S₀ n ≃ Hⁿ_cont(G_{K,S₀}, W)` (ContBridge's all-degree comparison). -/
def genHEquivAll (K : Type) [Field K] [NumberField K] (S₀ : Set (HeightOneSpectrum (𝓞 K)))
    (n : ℕ) : genH K S₀ n ≃ₗ[ZMod 2] continuousCohomology n (Wrep K S₀) := by
  have : LocallyCompactSpace (GKS K S₀) := locallyCompactSpace_GS K S₀
  have : ContinuousSMul (ZMod 2) (Wgen K S₀) :=
    ZInQ.Contrib.CloudB3RC53.ContBridge.continuousSMul_of_discrete (ZMod 2) (Wgen K S₀)
  exact (ZInQ.Contrib.CloudB3RC53.ContBridge.contCohomologyLinearEquiv
    (ZMod 2) (GKS K S₀) (Wgen K S₀) n).symm

/-- **`GlobalDegreeThreeVanishes` from the Milne print, with the degree-`3` identification against
the genuine `genH`**: `eG3 : Dsel.G.X 3 ≃ genH K S₀ 3` (the same kind as `eG`), composed with
`genHEquivAll 3`, and Milne ADT I.4.10 (`H³ = 0` for totally complex `K`). PROVED. -/
theorem globalDegreeThreeVanishes_of_milne_genH {K : Type} [Field K] [NumberField K]
    (h410 : MilneADT_I_4_10_totallyComplex) (hK : IsTotallyComplex K) {N r : ℕ}
    {D : Finset ℕ} (hN : N ≠ 0) (hr : r.Prime) (hD : ∀ p ∈ D, p.Prime)
    (Dsel : SelData (ZMod 2))
    (eG3 : Dsel.G.X 3 ≃ₗ[ZMod 2] genH K (primesAboveSet K (chargedPrimes N r D)) 3) :
    GlobalDegreeThreeVanishes Dsel :=
  globalDegreeThreeVanishes_of_milne h410 hK hN hr hD Dsel
    (eG3.trans (genHEquivAll K _ 3))

variable (K : Type) [Field K] [NumberField K]
  (Ew : ∀ w : HeightOneSpectrum (𝓞 K), WeierstrassCurve (w.adicCompletionIntegers K))
  [hEw : ∀ w, ((Ew w).baseChange (w.adicCompletion K)).IsElliptic]

open Classical in
/-- **`residualRankCounts_afterT'` with the degree-`3` identification against the genuine `genH`**:
`eG3 : Dsel.G.X 3 ≃ genH K S₀ 3` (the same kind as `eG`), discharged through
`globalDegreeThreeVanishes_of_milne_genH` (ContBridge's all-degree comparison and Milne ADT I.4.10).
PROVED. -/
def residualRankCounts_afterT''' (h410 : MilneADT_I_4_10_totallyComplex)
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
    -- the residual model and its identifications, in all degrees `[0, 3]`
    (Sloc : Set (HeightOneSpectrum (𝓞 K)))
    (Dsel : SelData (ZMod 2))
    [∀ n, Module.Finite (ZMod 2) (Dsel.G.X n)] [∀ n, Module.Finite (ZMod 2) (Dsel.U.X n)]
    [∀ n, Module.Finite (ZMod 2) (Dsel.L.X n)]
    (eG : ∀ n ∈ Finset.Icc (0 : ℤ) 2, Dsel.G.X n ≃ₗ[ZMod 2]
      genH K (primesAboveSet K (chargedPrimes N r D)) n.toNat)
    (eG3 : Dsel.G.X 3 ≃ₗ[ZMod 2] genH K (primesAboveSet K (chargedPrimes N r D)) 3)
    (hUm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.U.X n) ≤
      ∑ p ∈ chargedPrimes N r D,
        condSum K (genCondDimFun2 K Sloc cond (kummerDimOfCurves K Ew (kd2OfCurves K Ew))) p)
    (hLm : ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (Dsel.L.X (n - 1)) ≤
      ∑ p ∈ chargedPrimes N r D, genLocSum K Sloc p)
    -- the transfer after inverting `t`, with comparisons of complexes
    (P : CochainComplex (ModuleCat.{0} (PowerSeries (ZMod 2))) ℤ)
    [∀ i, Module.Free (PowerSeries (ZMod 2)) (P.X i)]
    [∀ i, Module.Finite (PowerSeries (ZMod 2)) (P.X i)] [P.IsStrictlyGE 0] [P.IsStrictlyLE 3]
    (ered : baseChangeCx (PowerSeries.constantCoeff : PowerSeries (ZMod 2) →+* ZMod 2) P ≅
      (selCx Dsel).toCC)
    (P' L : CochainComplex (ModuleCat.{0} (LaurentSeries (ZMod 2))) ℤ)
    [P'.IsStrictlyGE 0] [P'.IsStrictlyLE 3] [L.IsStrictlyGE 0] [L.IsStrictlyLE 3]
    [∀ i, Module.Finite (LaurentSeries (ZMod 2)) (P'.X i)]
    [∀ i, Module.Finite (LaurentSeries (ZMod 2)) (L.X i)]
    (ebc : P' ≅ baseChangeCx (algebraMap (PowerSeries (ZMod 2)) (LaurentSeries (ZMod 2))) P)
    (hLmin : ∀ i j x, (L.d i j).hom x ∈
      IsLocalRing.maximalIdeal (LaurentSeries (ZMod 2)) •
        (⊤ : Submodule (LaurentSeries (ZMod 2)) (L.X j)))
    (e : HomotopyEquiv L P') :
    ResidualRankCounts :=
  residualRankCounts_afterT' K Ew h410 h51 h28 h23 k α hα hK N hN A hA r hr D hD hDodd cond hcondD
    hfull w hw Sloc Dsel eG (globalDegreeThreeVanishes_of_milne_genH h410 hK hN hr hD Dsel eG3)
    hUm hLm P ered P' L ebc hLmin e

end ZInQ.Contrib.CloudB3RC53.GenuineInst

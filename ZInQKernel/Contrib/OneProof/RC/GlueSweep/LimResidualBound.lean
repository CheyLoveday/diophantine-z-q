import ZInQKernel.Contrib.CloudB3RC53.RankCounts.ResidualCountsFull
import ZInQKernel.Contrib.CloudB3RC53.RankCounts.ArchCounts
import ZInQKernel.Contrib.OneProof.RC.Limits.Lemmas
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.LimTransfer

/-!
# Lane RC22 (glue sweep, limits): Lemma `ex:limits-residual-bound` with the transfer discharged

Manuscript tex 4453–4648, Lemma `ex:limits-residual-bound`:
`N(E, A, j) ≤ 56 ω(2N) + 8A + 56j + 70`.

Lane RC6 (`RC/Limits/ResidualBound.lean`, `RC/Limits/Lemmas.lean`) proves the lemma
(`ex_limits_residual_bound`, `ResidualRankCounts.genericRank_le`) from the structure
`ResidualRankCounts`, whose fields are the counts behind (5.1) as numbers. In the tree,
`RankCounts.residualRankCounts_full` / `RankCounts.residualRankBound_full`
(`CloudB3RC53/RankCounts/ResidualCountsFull.lean`) already build the structure with `ram_sub`,
`global_le`, `places_length`, `places_deg`, `places_counts` and `cone` PROVED (from the PRINT leaves
Milne ADT I.4.10, I.5.1, I.2.3, I.2.8, the genuine places of `K` and the Selmer-cone model), but
still take the fields `transfer` (`genericRank`, `transfer`) and `arch_le` (`archTot`, `arch_le`)
as hypotheses. This file discharges `arch_le` with the tree's `RankCounts.archLe_proof`
(`archTotal K w = 4` at the complex place) and `transfer` with `transfer_residualDims_lim` /
`transfer_final_residualDims_lim` (`LimTransfer.lean`), so
that `N(E, A, j)` is the genuine residual quantity: the total dimension of the cohomology of the
original-support complex after reduction to the residue field of the local coefficient ring.
Every theorem here is PROVED from the remaining inputs listed in its docstring.
-/

namespace ZInQ.Manuscript.RC.GlueSweep.Lim

open CategoryTheory NumberField ZInQ.Manuscript.RC.Limits ZInQ.Contrib.CloudB3RC53
  ZInQ.Contrib.CloudB3RC53.RankCounts ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.ResidualTransfer

universe u

/-! ### Freeness of the Selmer cone model -/

/-- The Selmer cone `C^n = G^n ⊕ U^n ⊕ L^{n−1}` of free models is free (tex 4593–4597, the finite free
model of the cone (4.3)). PROVED; used to feed `cone_of_selmerModel` and the transfer. -/
theorem selCx_free_lim {S : Type u} [CommRing S] (D : SelData S)
    [∀ n, Module.Free S (D.G.X n)] [∀ n, Module.Free S (D.U.X n)] [∀ n, Module.Free S (D.L.X n)]
    (n : ℤ) : Module.Free S ((selCx D).toCC.X n) := by
  change Module.Free S (D.G.X n × D.U.X n × D.L.X (n - 1))
  infer_instance

/-- The Selmer cone `C^n = G^n ⊕ U^n ⊕ L^{n−1}` of finite models is finite (tex 4593–4597). PROVED;
used to feed `cone_of_selmerModel` and the transfer. -/
theorem selCx_finite_lim {S : Type u} [CommRing S] (D : SelData S)
    [∀ n, Module.Finite S (D.G.X n)] [∀ n, Module.Finite S (D.U.X n)]
    [∀ n, Module.Finite S (D.L.X n)] (n : ℤ) : Module.Finite S ((selCx D).toCC.X n) := by
  change Module.Finite S (D.G.X n × D.U.X n × D.L.X (n - 1))
  infer_instance

/-! ### The display (5.1) -/

open Classical in
/-- **The display (5.1)** (tex 4593–4610): the total rank of the finite free model `selCx Dsel` of
the smaller-support Selmer cone is at most `56 ω(2N) + 8A + 56j + 70`. PROVED, from the PRINT leaves
`MilneADT_I_4_10_totallyComplex`, `MilneADT_I_5_1_totallyComplex`, `MilneADT_I_2_8`,
`MilneADT_I_2_3_trivial`, `genus` and `kummer` (RC6's GLUE, genuine `h¹(G_{K,S_T}, 𝔽₂)`), Elliot's
table `hcond` (ELLIOT), and the model rank bounds `hG`, `hL` (tex 4593–4597); the archimedean
terms are those of an infinite place `wInf` (`archLe_proof`).

Consumers: RC6's `ex_limits_residual_bound_5_1` / `ResidualRankCounts.rankTot_le` and the tree's
`RankCounts.residualRankBound_full` read with `genericRank := rankTot` (its hypotheses `archTot`,
`arch_le` removed); dischargers: `RankCounts.residualRankBound_full`, `RankCounts.archLe_proof`. -/
theorem ex_limits_residual_bound_5_1_lim
    (h410 : MilneADT_I_4_10_totallyComplex) (h51 : MilneADT_I_5_1_totallyComplex)
    (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (K : Type) [Field K] [NumberField K] (k : ℤ) (α : 𝓞 K) (hα : IsQuadraticRadicand K k α)
    (hK : IsTotallyComplex K) (N : ℕ) (hN : N ≠ 0) (A : ℕ) (hA : k.natAbs.primeFactors.card ≤ A)
    (r : ℕ) (hr : r.Prime) (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime)
    (clDim : ℕ) (genus : clDim + 1 ≤ (ramifiedPrimes K k).card)
    (kummer : h1F2 K (primesAboveSet K (primeSetT N r D (ramifiedPrimes K k))) =
      (1 + ∑ p ∈ primeSetT N r D (ramifiedPrimes K k), nPlaces K p) + clDim)
    (cond : Ideal (𝓞 K) → LocalCondition) (condDim : Ideal (𝓞 K) → ℕ)
    (hcond : ∀ p ∈ chargedPrimes N r D, ∀ w ∈ placesList K cond condDim p,
      w.condDim = w.cond.dim w.deg)
    (wInf : InfinitePlace K)
    {S : Type} [CommRing S] [StrongRankCondition S] (Dsel : SelData S)
    [∀ n, Module.Free S (Dsel.G.X n)] [∀ n, Module.Finite S (Dsel.G.X n)]
    [∀ n, Module.Free S (Dsel.U.X n)] [∀ n, Module.Finite S (Dsel.U.X n)]
    [∀ n, Module.Free S (Dsel.L.X n)] [∀ n, Module.Finite S (Dsel.L.X n)] (s : Finset ℤ)
    (hG : ∑ n ∈ s, Module.finrank S (Dsel.G.X n) ≤
      hW K (primesAboveSet K (chargedPrimes N r D)) 0 +
        hW K (primesAboveSet K (chargedPrimes N r D)) 1 +
        hW K (primesAboveSet K (chargedPrimes N r D)) 2)
    (hL : ∑ n ∈ s, Module.finrank S (Dsel.U.X n) + ∑ n ∈ s, Module.finrank S (Dsel.L.X (n - 1)) ≤
      ∑ p ∈ chargedPrimes N r D, ((placesList K cond condDim p).map PlaceData.cost).sum +
        archTotal K wInf) :
    ∑ n ∈ s, Module.finrank S ((selCx Dsel).X n) ≤
      56 * (2 * N).primeFactors.card + 8 * A + 56 * D.card + 70 :=
  residualRankBound_full K h410 h51 h28 h23 k α hα hK N hN A hA r hr D hD clDim genus kummer
    cond condDim hcond (archTotal K wInf) (archLe_proof K wInf (hK.isComplex wInf)) Dsel s _ rfl
    hG hL _ le_rfl

/-! ### The lemma with the transfer discharged -/

open Classical in
/-- **Lemma `ex:limits-residual-bound`: `N(E, A, j) ≤ 56 ω(2N) + 8A + 56j + 70`** (tex 4453–4648),
with `N(E, A, j) = ∑_{n ∈ s} dim_k Hⁿ(k ⊗_S C)` the total residual cohomology dimension of the
original-support complex `C` over the local coefficient ring `S` (tex 4637–4647; the rank of a
minimal model of `C`). PROVED, from:
* the PRINT leaves `MilneADT_I_4_10_totallyComplex`, `MilneADT_I_5_1_totallyComplex` (global,
  stated in the tree for the genuine `G_{K,S}`) and `MilneADT_I_2_8`, `MilneADT_I_2_3_trivial`
  (local, RC6's `LocalPrints`);
* `genus` (tex 4494–4517, ELLIOT's genus argument) and `kummer` (tex 4482–4492, Kummer theory and
  the `S`-unit theorem), RC6's GLUE, for the genuine `h¹(G_{K,S_T}, 𝔽₂)` (`clDim` undefined in Lean);
* the local conditions `cond`, `condDim` at the genuine places of `K` and Elliot's table `hcond`
  (tex 4551–4573, ELLIOT); the archimedean terms are those of an infinite place `wInf` of `K`
  (`archTotal K wInf = 4` at the complex place, the tree's `archLe_proof`, tex 4584–4591);
* finite free models `G`, `U`, `L` of the old Selmer data `T.D` over `S` with the rank bounds `hG`
  (global part at most `h⁰ + h¹ + h²` of the genuine `G_{K,S₀}`) and `hL` (local part at most the
  place costs plus the archimedean terms `archTotal K wInf`) (tex 4593–4597);
* the support change `T` with the GLUE input `SupportChangeInput` (Nekovář, *Selmer complexes*,
  Prop. 7.8.8(ii), tex 4612–4618) and bounded free Selmer models;
* the original-support complex `C` (bounded finite free) with the active comparison
  `jact : C ⟶ selCx T.Dp` whose cone is contractible after inverting `t` (`hact`, tex 4619–4631).

Consumers: RC6's `ex_limits_residual_bound` / `ResidualRankCounts.genericRank_le`, and the tree's
`RankCounts.residualRankBound_full` (its hypotheses `genericRank`, `transfer`, `archTot`, `arch_le`
removed); dischargers: `RankCounts.residualRankBound_full`, `RankCounts.archLe_proof`,
`transfer_residualDims_lim`. -/
theorem ex_limits_residual_bound_lim
    (h410 : MilneADT_I_4_10_totallyComplex) (h51 : MilneADT_I_5_1_totallyComplex)
    (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (K : Type) [Field K] [NumberField K] (k : ℤ) (α : 𝓞 K) (hα : IsQuadraticRadicand K k α)
    (hK : IsTotallyComplex K) (N : ℕ) (hN : N ≠ 0) (A : ℕ) (hA : k.natAbs.primeFactors.card ≤ A)
    (r : ℕ) (hr : r.Prime) (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime)
    (clDim : ℕ) (genus : clDim + 1 ≤ (ramifiedPrimes K k).card)
    (kummer : h1F2 K (primesAboveSet K (primeSetT N r D (ramifiedPrimes K k))) =
      (1 + ∑ p ∈ primeSetT N r D (ramifiedPrimes K k), nPlaces K p) + clDim)
    (cond : Ideal (𝓞 K) → LocalCondition) (condDim : Ideal (𝓞 K) → ℕ)
    (hcond : ∀ p ∈ chargedPrimes N r D, ∀ w ∈ placesList K cond condDim p,
      w.condDim = w.cond.dim w.deg)
    (wInf : InfinitePlace K)
    {S : Type} [CommRing S] [IsLocalRing S]
    (T : SupportChangeData S) (H : SupportChangeUnramified T) (hSC : SupportChangeInput T H)
    [∀ n, Module.Free S (T.D.G.X n)] [∀ n, Module.Finite S (T.D.G.X n)]
    [∀ n, Module.Free S (T.D.U.X n)] [∀ n, Module.Finite S (T.D.U.X n)]
    [∀ n, Module.Free S (T.D.L.X n)] [∀ n, Module.Finite S (T.D.L.X n)]
    [∀ n, Module.Free S ((selCx T.Dp).toCC.X n)] (a b : ℤ)
    [(selCx T.D).toCC.IsStrictlyGE a] [(selCx T.D).toCC.IsStrictlyLE b]
    [(selCx T.Dp).toCC.IsStrictlyGE a] [(selCx T.Dp).toCC.IsStrictlyLE b] (s : Finset ℤ)
    (hG : ∑ n ∈ s, Module.finrank S (T.D.G.X n) ≤
      hW K (primesAboveSet K (chargedPrimes N r D)) 0 +
        hW K (primesAboveSet K (chargedPrimes N r D)) 1 +
        hW K (primesAboveSet K (chargedPrimes N r D)) 2)
    (hL : ∑ n ∈ s, Module.finrank S (T.D.U.X n) + ∑ n ∈ s, Module.finrank S (T.D.L.X (n - 1)) ≤
      ∑ p ∈ chargedPrimes N r D, ((placesList K cond condDim p).map PlaceData.cost).sum +
        archTotal K wInf)
    (C : CochainComplex (ModuleCat.{0} S) ℤ) [C.IsStrictlyGE a] [C.IsStrictlyLE b]
    [∀ i, Module.Free S (C.X i)] [∀ i, Module.Finite S (C.X i)]
    (jact : C ⟶ (selCx T.Dp).toCC)
    (hact : Nonempty (Homotopy (𝟙 (CochainComplex.mappingCone jact)) 0)) :
    ∑ n ∈ s, Module.finrank (IsLocalRing.ResidueField S) (residualCohomology S C n) ≤
      56 * (2 * N).primeFactors.card + 8 * A + 56 * D.card + 70 := by
  have : ∀ n, Module.Free S ((selCx T.D).toCC.X n) := selCx_free_lim T.D
  have : ∀ n, Module.Finite S ((selCx T.D).toCC.X n) := selCx_finite_lim T.D
  exact residualRankBound_full K h410 h51 h28 h23 k α hα hK N hN A hA r hr D hD clDim genus kummer
    cond condDim hcond (archTotal K wInf) (archLe_proof K wInf (hK.isComplex wInf)) T.D s _ rfl
    hG hL _
    (transfer_residualDims_lim T H hSC a b C jact hact s)

open Classical in
/-- **Lemma `ex:limits-residual-bound`, final form** (tex 4453–4648): as
`ex_limits_residual_bound_lim`, with the original-support complex `C(U') = selCx (restrictData T.Dp f)`
obtained from the unramified-at-active model by the change of local conditions
`0 → U' → T.Dp.U → W → 0` at the active places, and the contractibility of the active comparison
cone discharged from the acyclicity of the singular quotient `W` (tex 4619–4631; the tree's
`hact_of_singularQuotient`, with `twoTerm_acyclic` and `activeSingular_bijective` for the
two-term singular blocks `[M --((1+t)^e − 1)φ--> M]`, `e` odd). PROVED, from the inputs of
`ex_limits_residual_bound_lim` other than `C`, `jact`, `hact`, plus the short exact sequence of
local conditions (`hfg`, `hinj`, `hsurj`, `hex`), `hW : W` acyclic, and bounded finite free models
of `C(U')`. The remaining GLUE/PRINT/ELLIOT inputs are exactly: the four Milne PRINT leaves,
`genus`, `kummer`, `hcond`, `hG`, `hL`, `SupportChangeInput`.

Consumers: RC6's `ex_limits_residual_bound` / `ResidualRankCounts.genericRank_le`, the tree's
`RankCounts.residualRankBound_full` (`genericRank`, `transfer`, `archTot`, `arch_le` removed) and
`ResidualTransfer.transfer_final` (`L`, `hLmin`, `eL` removed); dischargers:
`RankCounts.residualRankBound_full`, `RankCounts.archLe_proof`,
`transfer_final_residualDims_lim`. -/
theorem ex_limits_residual_bound_final_lim
    (h410 : MilneADT_I_4_10_totallyComplex) (h51 : MilneADT_I_5_1_totallyComplex)
    (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (K : Type) [Field K] [NumberField K] (k : ℤ) (α : 𝓞 K) (hα : IsQuadraticRadicand K k α)
    (hK : IsTotallyComplex K) (N : ℕ) (hN : N ≠ 0) (A : ℕ) (hA : k.natAbs.primeFactors.card ≤ A)
    (r : ℕ) (hr : r.Prime) (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime)
    (clDim : ℕ) (genus : clDim + 1 ≤ (ramifiedPrimes K k).card)
    (kummer : h1F2 K (primesAboveSet K (primeSetT N r D (ramifiedPrimes K k))) =
      (1 + ∑ p ∈ primeSetT N r D (ramifiedPrimes K k), nPlaces K p) + clDim)
    (cond : Ideal (𝓞 K) → LocalCondition) (condDim : Ideal (𝓞 K) → ℕ)
    (hcond : ∀ p ∈ chargedPrimes N r D, ∀ w ∈ placesList K cond condDim p,
      w.condDim = w.cond.dim w.deg)
    (wInf : InfinitePlace K)
    {S : Type} [CommRing S] [IsLocalRing S]
    (T : SupportChangeData S) (H : SupportChangeUnramified T) (hSC : SupportChangeInput T H)
    [∀ n, Module.Free S (T.D.G.X n)] [∀ n, Module.Finite S (T.D.G.X n)]
    [∀ n, Module.Free S (T.D.U.X n)] [∀ n, Module.Finite S (T.D.U.X n)]
    [∀ n, Module.Free S (T.D.L.X n)] [∀ n, Module.Finite S (T.D.L.X n)]
    [∀ n, Module.Free S ((selCx T.Dp).toCC.X n)] (a b : ℤ)
    [(selCx T.D).toCC.IsStrictlyGE a] [(selCx T.D).toCC.IsStrictlyLE b]
    [(selCx T.Dp).toCC.IsStrictlyGE a] [(selCx T.Dp).toCC.IsStrictlyLE b] (s : Finset ℤ)
    (hG : ∑ n ∈ s, Module.finrank S (T.D.G.X n) ≤
      hW K (primesAboveSet K (chargedPrimes N r D)) 0 +
        hW K (primesAboveSet K (chargedPrimes N r D)) 1 +
        hW K (primesAboveSet K (chargedPrimes N r D)) 2)
    (hL : ∑ n ∈ s, Module.finrank S (T.D.U.X n) + ∑ n ∈ s, Module.finrank S (T.D.L.X (n - 1)) ≤
      ∑ p ∈ chargedPrimes N r D, ((placesList K cond condDim p).map PlaceData.cost).sum +
        archTotal K wInf)
    (U' W : GCx S) (f : GHom U' T.Dp.U) (g : GHom T.Dp.U W)
    (hfg : ∀ i (u : U'.X i), g.f i i rfl (f.f i i rfl u) = 0)
    (hinj : ∀ i, Function.Injective (f.f i i rfl)) (hsurj : ∀ i, Function.Surjective (g.f i i rfl))
    (hex : ∀ i (u : T.Dp.U.X i), g.f i i rfl u = 0 → ∃ u', f.f i i rfl u' = u)
    (hW : W.toCC.Acyclic)
    [(selCx (restrictData T.Dp f)).toCC.IsStrictlyGE a]
    [(selCx (restrictData T.Dp f)).toCC.IsStrictlyLE b]
    [∀ n, Module.Free S ((selCx (restrictData T.Dp f)).toCC.X n)]
    [∀ n, Module.Finite S ((selCx (restrictData T.Dp f)).toCC.X n)] :
    ∑ n ∈ s, Module.finrank (IsLocalRing.ResidueField S)
        (residualCohomology S (selCx (restrictData T.Dp f)).toCC n) ≤
      56 * (2 * N).primeFactors.card + 8 * A + 56 * D.card + 70 := by
  have : ∀ n, Module.Free S ((selCx T.D).toCC.X n) := selCx_free_lim T.D
  have : ∀ n, Module.Finite S ((selCx T.D).toCC.X n) := selCx_finite_lim T.D
  exact residualRankBound_full K h410 h51 h28 h23 k α hα hK N hN A hA r hr D hD clDim genus kummer
    cond condDim hcond (archTotal K wInf) (archLe_proof K wInf (hK.isComplex wInf)) T.D s _ rfl
    hG hL _
    (transfer_final_residualDims_lim T H hSC a b U' W f g hfg hinj hsurj hex hW s)

end ZInQ.Manuscript.RC.GlueSweep.Lim

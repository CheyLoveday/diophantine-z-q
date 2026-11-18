import ZInQKernel.Contrib.CloudB3RC53.Mattuck.Residual
import ZInQKernel.Contrib.CloudB3RC53.GenuineInst.Derivative
import ZInQKernel.Contrib.CloudB3RC53.GenuineInst.GlobalCounts
import ZInQKernel.Contrib.CloudB3RC53.GenuineInst.Transfer

/-!
# Mattuck, part 7: RC6's residual counts from the genuine complexes

Manuscript `diophantine_zq.tex`, Lemma `ex:limits-residual-bound`, tex 4453–4648.

`residualRankCounts_genuine`: `residualRankCounts_mattuck` with its three Selmer-cone inputs
supplied by the genuine producers:

* `hG` by `hG_of_genuineModel` (the global part of the residual model is degreewise the genuine
  `Hⁿ(G_{K,S₀}, W)`, `n ∈ [0, 2]`);
* `hL` by `hL_of_genuineModel2` (the condition and local parts of the residual model are bounded by
  the genuine condition and local cohomology dimensions at the places above the charged primes,
  with the old-Kummer dimension `kummerDimOfCurves` — Mattuck at every place);
* `transfer` by `transfer_final_genuine` (the genuine support change of Nekovář 7.8.8(ii), PRINT
  `NekovarProp788ii`, with the residual model as the bounded free model `P₀ = C(Dsel)` of the
  smaller-support genuine Selmer complex and `L` a minimal model of the original-support one).

The remaining inputs are the residual-model identifications (`eG`, `hUm`, `hLm`, the
quasi-isomorphism `pP` and the minimal model `L`), the condition assignment and local models (as in
`residualRankCounts_mattuck`), the support-change data of `transfer_final_genuine`, and the PRINT
leaves.

Caveat: the supports are not forced to agree. In the intended instance the smaller support `S` of
the support change, the support `Sloc` of the local counts and the support of `eG` are all
`primesAboveSet K (chargedPrimes N r D)`, with `M` the residual module `W`; the statement takes them
as independent parameters, so a consumer must supply consistent data.

**Classification.** PROVED (from the inputs listed).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.Mattuck

open NumberField IsDedekindDomain CategoryTheory ZInQ.Manuscript.RC.Limits
  ZInQ.Contrib.CloudB3RC53.RankCounts ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Manuscript.RC.SelmerComplex ZInQ.Contrib.CloudB3RC53.GenuineInst
  ZInQ.Contrib.CloudB3RC53.SelmerDuality

variable (K : Type) [Field K] [NumberField K]
  (Ew : ∀ w : HeightOneSpectrum (𝓞 K), WeierstrassCurve (w.adicCompletionIntegers K))
  [hEw : ∀ w, ((Ew w).baseChange (w.adicCompletion K)).IsElliptic]

open Classical in
/-- **RC6's `ResidualRankCounts` from the genuine complexes** (tex 4453–4648): the counts `kummer`,
`hcond` (Mattuck at every place), `hG`, `hL` and `transfer` all supplied by PROVED results on the
genuine Selmer and local complexes, from the residual-model identifications and the support-change
data listed in the module docstring. PROVED. -/
def residualRankCounts_genuine (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (h788 : NekovarProp788ii K)
    (k : ℤ) (α : 𝓞 K) (hα : IsQuadraticRadicand K k α)
    (hK : IsTotallyComplex K) (N : ℕ) (hN : N ≠ 0) (A : ℕ) (hA : k.natAbs.primeFactors.card ≤ A)
    (r : ℕ) (hr : r.Prime) (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime) (hDodd : ∀ p ∈ D, p ≠ 2)
    (cond : Ideal (𝓞 K) → LocalCondition)
    (hcondD : ∀ P : Ideal (𝓞 K), cond P = .derivRelaxed → ∃ q ∈ D, P ∈ primesAbove K q)
    (hfull : ∀ w : HeightOneSpectrum (𝓞 K), cond w.asIdeal = .oldKummer →
      Nat.card (Submodule.torsionBy ℤ ((Ew w).baseChange (w.adicCompletion K)).toAffine.Point 2) =
        4)
    (w : InfinitePlace K) (hw : w.IsComplex)
    -- the residual model and its identifications
    (Sloc : Set (HeightOneSpectrum (𝓞 K)))
    (Dsel : SelData (ZMod 2))
    [∀ n, Module.Finite (ZMod 2) (Dsel.G.X n)] [∀ n, Module.Finite (ZMod 2) (Dsel.U.X n)]
    [∀ n, Module.Finite (ZMod 2) (Dsel.L.X n)]
    (s : Finset ℤ) (hs : s ⊆ Finset.Icc 0 2)
    (eG : ∀ n ∈ s, Dsel.G.X n ≃ₗ[ZMod 2]
      genH K (primesAboveSet K (chargedPrimes N r D)) n.toNat)
    (hUm : ∑ n ∈ s, Module.finrank (ZMod 2) (Dsel.U.X n) ≤ ∑ p ∈ chargedPrimes N r D,
      condSum K (genCondDimFun2 K Sloc cond (kummerDimOfCurves K Ew (kd2OfCurves K Ew))) p)
    (hLm : ∑ n ∈ s, Module.finrank (ZMod 2) (Dsel.L.X (n - 1)) ≤
      ∑ p ∈ chargedPrimes N r D, genLocSum K Sloc p)
    -- the support change (`transfer_final_genuine`)
    {S S' : Set (HeightOneSpectrum (𝓞 K))} (hSS' : S ⊆ S') (pr : ℕ)
    (hset : NekovarFiniteSetting K S pr (ZMod 2)) (hS' : S'.Finite)
    (M : Type) [AddCommGroup M] [Module (ZMod 2) M] [DistribMulAction (GKS K S) M]
    [SMulCommClass (GKS K S) (ZMod 2) M] [TopologicalSpace M] [DiscreteTopology M]
    [ContinuousSMul (GKS K S) M] [Finite M]
    (ψ : ∀ q : NewPlaces K S S', GUr K q.1 →ₜ* GKS K S)
    (hψ : ∀ (q : NewPlaces K S S') g, locMap K S q.1 g = ψ q (urRes K q.1 g))
    (Δ : GaloisLocalConditions K S (ZMod 2) M)
    (Dfull : SelData (ZMod 2)) (W : GCx (ZMod 2))
    (f : GHom (galoisSupportData K hSS' (ZMod 2) M ψ hψ Δ).Dp.U Dfull.U)
    (g : GHom Dfull.U W)
    (hDp : (galoisSupportData K hSS' (ZMod 2) M ψ hψ Δ).Dp = restrictData Dfull f)
    (hfg : ∀ i (u : (galoisSupportData K hSS' (ZMod 2) M ψ hψ Δ).Dp.U.X i),
      g.f i i rfl (f.f i i rfl u) = 0)
    (hinj : ∀ i, Function.Injective (f.f i i rfl)) (hsurj : ∀ i, Function.Surjective (g.f i i rfl))
    (hex : ∀ i (u : Dfull.U.X i), g.f i i rfl u = 0 → ∃ u', f.f i i rfl u' = u)
    (hW : W.toCC.Acyclic) (a b : ℤ)
    [(selCx Dsel).toCC.IsStrictlyGE a] [(selCx Dsel).toCC.IsStrictlyLE b]
    (pP : (selCx Dsel).toCC ⟶ (selCx (galoisSupportData K hSS' (ZMod 2) M ψ hψ Δ).D).toCC)
    [QuasiIso pP]
    (L : CochainComplex (ModuleCat.{0} (ZMod 2)) ℤ) [L.IsStrictlyGE a] [L.IsStrictlyLE b]
    [∀ i, Module.Finite (ZMod 2) (L.X i)]
    (hLmin : ∀ i j x, (L.d i j).hom x ∈
      IsLocalRing.maximalIdeal (ZMod 2) • (⊤ : Submodule (ZMod 2) (L.X j)))
    (pL : L ⟶ (selCx Dfull).toCC) [QuasiIso pL] :
    ResidualRankCounts :=
  haveI : ∀ i, Module.Finite (ZMod 2) ((selCx Dsel).toCC.X i) := fun i => by
    change Module.Finite (ZMod 2) (Dsel.G.X i × Dsel.U.X i × Dsel.L.X (i - 1))
    infer_instance
  residualRankCounts_mattuck K Ew h410 h51 h28 h23 k α hα hK N hN A hA r hr D hD hDodd cond hcondD
    hfull w hw Dsel s (∑ n ∈ s, Module.finrank (ZMod 2) ((selCx Dsel).X n)) rfl
    (hG_of_genuineModel K _ Dsel s hs eG)
    (hL_of_genuineModel2 K Sloc hr hD cond (kummerDimOfCurves K Ew (kd2OfCurves K Ew)) Dsel s
      (archTotal K w) hUm hLm)
    (∑ n ∈ s, Module.finrank (ZMod 2) (L.X n))
    (transfer_final_genuine K h788 hSS' pr (ZMod 2) hset hS' M ψ hψ Δ Dfull W f g hDp hfg hinj
      hsurj hex hW a b (selCx Dsel).toCC pP L hLmin pL s _ _ rfl rfl)

end ZInQ.Contrib.CloudB3RC53.Mattuck

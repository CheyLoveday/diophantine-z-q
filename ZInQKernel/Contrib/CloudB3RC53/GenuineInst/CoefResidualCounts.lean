import ZInQKernel.Contrib.CloudB3RC53.GenuineInst.CoefResidual
import ZInQKernel.Contrib.CloudB3RC53.Mattuck.ResidualGenuine

/-!
# Genuine instantiations, part 20: RC6's residual counts at the actual coefficient module

Manuscript `diophantine_zq.tex`, Lemma `ex:limits-residual-bound`, tex 4453–4648, with the residual
representation `W = E[2] = M_i / 𝔪 M_i` (tex 4479–4480, 4521–4531).

* `ResidualM W j α`: the residual module `𝔽₂ ⊗_{A_{j+1}} M_{j+1}` of the actual coefficient module
  `M_{j+1} = Mcoef K S W (j+1) α`, as a discrete `𝔽₂[G_{K,S}]`-module (action `id ⊗ α(σ)(id ⊗ σ)`);
* `smul_residualM_eq`: under `FullTorsion` at `2^{j+1}`, `2^j`, `2` and trivial action on
  `E(K_S)[2]`, the action on `ResidualM` is trivial (`residualFin2_resAct`);
* `residualMEquivWgen`: then `ResidualM W j α ≅ W = 𝔽₂²` (trivial action) as `𝔽₂[G_{K,S}]`-modules,
  and `residualCohEquiv`: `Hⁿ_cont(G_{K,S}, ResidualM W j α) ≅ Hⁿ_cont(G_{K,S}, W) = genH K S n`;
* `ResidualCohAtActual` (node, PROVED): the cohomology comparison;
* `residualRankCounts_actual`: `residualRankCounts_genuine` with the global part of the residual
  model identified with the continuous cohomology of the actual residual module and with the
  actual residual module as the coefficient module of the support change;
* Non-vacuity of the new hypotheses: `residualFin2_hyps_cubicCurve` (`FullTorsion` and trivial
  action) and `residualM_instances_cubicCurve` (the instance arguments).

**Classification.** Definitions and PROVED statements (from the inputs listed; the remaining
inputs are those of `residualRankCounts_genuine`).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.GenuineInst

open TensorProduct CategoryTheory NumberField IsDedekindDomain WeierstrassCurve
  ZInQ.Manuscript.RC.HeegnerAlgebra ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.SelmerComplex

section ResidualModule

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) (j : ℕ) (α : GKS K S →* (Acoef (j + 1))ˣ)

/-- **The residual module of the actual `M_{j+1}`**, `𝔽₂ ⊗_{A_{j+1}} M_{j+1}` (a type synonym
carrying the residual `G_{K,S}`-action). -/
def ResidualM : Type := ZMod 2 ⊗[Acoef (j + 1)] Mcoef K S W (j + 1) α

instance : AddCommGroup (ResidualM W j α) :=
  inferInstanceAs (AddCommGroup (ZMod 2 ⊗[Acoef (j + 1)] Mcoef K S W (j + 1) α))

instance : Module (ZMod 2) (ResidualM W j α) :=
  inferInstanceAs (Module (ZMod 2) (ZMod 2 ⊗[Acoef (j + 1)] Mcoef K S W (j + 1) α))

/-- The residual action `σ ↦ id ⊗ α(σ)(id ⊗ σ)`. -/
instance : DistribMulAction (GKS K S) (ResidualM W j α) where
  smul σ x := resAct (j + 1) α (TorsS K S W ((2 ^ (j + 1) : ℕ) : ℤ)) σ x
  one_smul x := by
    change LinearMap.lTensor (ZMod 2) (CoefMod.act (Acoef (j + 1)) α _ 1) x = x
    rw [CoefMod.act_one, LinearMap.lTensor_id]
    rfl
  mul_smul σ τ x := by
    change LinearMap.lTensor (ZMod 2) (CoefMod.act (Acoef (j + 1)) α _ (σ * τ)) x =
      LinearMap.lTensor (ZMod 2) (CoefMod.act (Acoef (j + 1)) α _ σ)
        (LinearMap.lTensor (ZMod 2) (CoefMod.act (Acoef (j + 1)) α _ τ) x)
    rw [CoefMod.act_mul, LinearMap.lTensor_comp]
    rfl
  smul_zero σ := map_zero (resAct (j + 1) α (TorsS K S W ((2 ^ (j + 1) : ℕ) : ℤ)) σ)
  smul_add σ := map_add (resAct (j + 1) α (TorsS K S W ((2 ^ (j + 1) : ℕ) : ℤ)) σ)

omit [NumberField K] in
theorem residualM_smul_def (σ : GKS K S) (x : ResidualM W j α) :
    σ • x = resAct (j + 1) α (TorsS K S W ((2 ^ (j + 1) : ℕ) : ℤ)) σ x := rfl

instance : SMulCommClass (GKS K S) (ZMod 2) (ResidualM W j α) where
  smul_comm σ c x :=
    ZMod.map_smul (resAct (j + 1) α (TorsS K S W ((2 ^ (j + 1) : ℕ) : ℤ)) σ).toAddMonoidHom c x

instance : TopologicalSpace (ResidualM W j α) := ⊥

instance : DiscreteTopology (ResidualM W j α) := ⟨rfl⟩

instance : ContinuousAdd (ResidualM W j α) := ⟨continuous_of_discreteTopology⟩

instance : ContinuousConstSMul (ZMod 2) (ResidualM W j α) :=
  ⟨fun _ => continuous_of_discreteTopology⟩

omit [NumberField K] in
/-- **The residual action is trivial** when `E(K_S)[2]` is rational (tex 4479–4480), under
`FullTorsion` at `2^{j+1}`, `2^j`, `2`. PROVED. -/
theorem smul_residualM_eq (hT : FullTorsion K S W (2 ^ (j + 1))) (hM : FullTorsion K S W (2 ^ j))
    (h2 : FullTorsion K S W 2)
    (htriv : ∀ (σ : GKS K S) (P : TorsS K S W ((2 : ℕ) : ℤ)), σ • P = P)
    (σ : GKS K S) (x : ResidualM W j α) : σ • x = x :=
  (residualFin2 j α hT hM h2).injective (residualFin2_resAct j α hT hM h2 htriv σ x)

omit [NumberField K] in
/-- The residual module is a discrete `G_{K,S}`-module (the action is trivial). PROVED. -/
theorem continuousSMul_residualM (hT : FullTorsion K S W (2 ^ (j + 1)))
    (hM : FullTorsion K S W (2 ^ j)) (h2 : FullTorsion K S W 2)
    (htriv : ∀ (σ : GKS K S) (P : TorsS K S W ((2 : ℕ) : ℤ)), σ • P = P) :
    ContinuousSMul (GKS K S) (ResidualM W j α) := by
  refine ⟨?_⟩
  have : (fun p : GKS K S × ResidualM W j α => p.1 • p.2) = Prod.snd :=
    funext fun p => smul_residualM_eq W j α hT hM h2 htriv p.1 p.2
  rw [this]
  exact continuous_snd

omit [NumberField K] in
/-- The residual module is finite (`≅ 𝔽₂²`). PROVED. -/
theorem finite_residualM (hT : FullTorsion K S W (2 ^ (j + 1))) (hM : FullTorsion K S W (2 ^ j))
    (h2 : FullTorsion K S W 2) : Finite (ResidualM W j α) :=
  Finite.of_equiv _ (residualFin2 j α hT hM h2).toEquiv.symm

/-- **`ResidualM W j α ≅ W = 𝔽₂²`** (`𝔽₂`-linearly). -/
def residualMEquivWgen (hT : FullTorsion K S W (2 ^ (j + 1))) (hM : FullTorsion K S W (2 ^ j))
    (h2 : FullTorsion K S W 2) : ResidualM W j α ≃ₗ[ZMod 2] Wgen K S :=
  (residualLinearFin2 j α hT hM h2).trans (LinearEquiv.finTwoArrow (ZMod 2) (ZMod 2))

/-- **`C^•_cont(G_{K,S}, ResidualM) ≅ C^•_cont(G_{K,S}, W)`**: the cochain isomorphism induced by
the equivariant `residualMEquivWgen` (both actions trivial). -/
def residualCochainsIso (hT : FullTorsion K S W (2 ^ (j + 1))) (hM : FullTorsion K S W (2 ^ j))
    (h2 : FullTorsion K S W 2)
    (htriv : ∀ (σ : GKS K S) (P : TorsS K S W ((2 : ℕ) : ℤ)), σ • P = P) :
    letI := continuousSMul_residualM W j α hT hM h2 htriv
    contCochains (ZMod 2) (GKS K S) (ResidualM W j α) ≅ contCochains (ZMod 2) (GKS K S) (Wgen K S) :=
  letI := continuousSMul_residualM W j α hT hM h2 htriv
  { hom := contCochainsMap (ContinuousMonoidHom.id _)
      (residualMEquivWgen W j α hT hM h2).toLinearMap continuous_of_discreteTopology
      (fun σ m => by rw [smul_residualM_eq W j α hT hM h2 htriv]; rfl)
    inv := contCochainsMap (ContinuousMonoidHom.id _)
      (residualMEquivWgen W j α hT hM h2).symm.toLinearMap continuous_of_discreteTopology
      (fun σ m => (smul_residualM_eq W j α hT hM h2 htriv σ _).symm)
    hom_inv_id := by
      rw [← contCochainsMap_comp]
      rw [← contCochainsMap_id (ZMod 2) (GKS K S) (ResidualM W j α)]
      congr 1
      exact LinearMap.ext fun x => LinearEquiv.symm_apply_apply _ x
    inv_hom_id := by
      rw [← contCochainsMap_comp]
      rw [← contCochainsMap_id (ZMod 2) (GKS K S) (Wgen K S)]
      congr 1
      exact LinearMap.ext fun x => (residualMEquivWgen W j α hT hM h2).apply_symm_apply x }

/-- **`Hⁿ_cont(G_{K,S}, 𝔽₂ ⊗ M_{j+1}) ≅ Hⁿ_cont(G_{K,S}, W) = genH K S n`**: the continuous
cohomology of the actual residual module is the genuine cohomology with coefficients `W = 𝔽₂²`. -/
def residualCohIso (hT : FullTorsion K S W (2 ^ (j + 1))) (hM : FullTorsion K S W (2 ^ j))
    (h2 : FullTorsion K S W 2)
    (htriv : ∀ (σ : GKS K S) (P : TorsS K S W ((2 : ℕ) : ℤ)), σ • P = P) (n : ℕ) :
    letI := continuousSMul_residualM W j α hT hM h2 htriv
    contCohomology (ZMod 2) (GKS K S) (ResidualM W j α) n ≅ genH K S n :=
  letI := continuousSMul_residualM W j α hT hM h2 htriv
  HomologicalComplex.homologyMapIso (residualCochainsIso W j α hT hM h2 htriv) n

/-- **Non-vacuity of the instance arguments at the actual residual module**: for
`y² = (x − e₁)(x − e₂)(x − e₃)` with distinct `e_k ∈ K`, every `S` and every character
`χ : G_{K,S} → A_1^×`, the residual module of `M_1` is a finite discrete `G_{K,S}`-module. PROVED. -/
theorem residualM_instances_cubicCurve {e₁ e₂ e₃ : K} (h12 : e₁ ≠ e₂) (h13 : e₁ ≠ e₃)
    (h23 : e₂ ≠ e₃) (χ : GKS K S →* (Acoef (0 + 1))ˣ) :
    ContinuousSMul (GKS K S) (ResidualM (cubicCurve e₁ e₂ e₃) 0 χ) ∧
      Finite (ResidualM (cubicCurve e₁ e₂ e₃) 0 χ) :=
  have h := residualFin2_hyps_cubicCurve (S := S) h12 h13 h23
  ⟨continuousSMul_residualM _ 0 χ h.1 h.2.1 h.2.2.1 h.2.2.2,
    finite_residualM _ 0 χ h.1 h.2.1 h.2.2.1⟩

end ResidualModule

section Node

/-- **Node: the cohomology of the actual residual module is the genuine `Hⁿ(G_{K,S}, 𝔽₂²)`.**
Manuscript tex 4479–4480 and 4521–4531 (`h⁰, h¹, h²` of `G_{K,S₀}` with coefficients `W = E[2]`,
`W = 𝔽₂²` with trivial action). Claim: for every number field `K`, `S`, curve `E`, `j` and
character `χ : G_{K,S} → A_{j+1}^×`, under `FullTorsion` at `2^{j+1}`, `2^j`, `2` and trivial
action on `E(K_S)[2]`, the residual module `𝔽₂ ⊗_{A_{j+1}} M_{j+1}` is a discrete
`G_{K,S}`-module and `Hⁿ_cont(G_{K,S}, 𝔽₂ ⊗ M_{j+1}) ≅ genH K S n` for every `n`. Kind: PROVED
(`residualCohAtActual_proof`). -/
def ResidualCohAtActual : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
    (E : WeierstrassCurve K) (j : ℕ) (χ : GKS K S →* (Acoef (j + 1))ˣ)
    (hT : FullTorsion K S E (2 ^ (j + 1))) (hM : FullTorsion K S E (2 ^ j))
    (h2 : FullTorsion K S E 2)
    (htriv : ∀ (σ : GKS K S) (P : TorsS K S E ((2 : ℕ) : ℤ)), σ • P = P) (n : ℕ),
    letI := continuousSMul_residualM E j χ hT hM h2 htriv
    Nonempty (contCohomology (ZMod 2) (GKS K S) (ResidualM E j χ) n ≅ genH K S n)

theorem residualCohAtActual_proof : ResidualCohAtActual := by
  intro K _ _ S E j χ hT hM h2 htriv n
  exact ⟨residualCohIso E j χ hT hM h2 htriv n⟩

end Node

section Counts

open ZInQ.Manuscript.RC.Limits ZInQ.Contrib.CloudB3RC53.RankCounts
  ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.Mattuck

variable (K : Type) [Field K] [NumberField K]
  (Ew : ∀ w : HeightOneSpectrum (𝓞 K), WeierstrassCurve (w.adicCompletionIntegers K))
  [hEw : ∀ w, ((Ew w).baseChange (w.adicCompletion K)).IsElliptic]

open Classical in
/-- **RC6's residual counts at the actual coefficient module** (tex 4453–4648, with `W = E[2] =
M_i / 𝔪 M_i`, tex 4479–4480, 4521–4531): `residualRankCounts_genuine` with

* the global part of the residual model identified (`eGact`) with the continuous cohomology
  `Hⁿ_cont(G_{K,S₀}, 𝔽₂ ⊗_{A_{j+1}} M_{j+1})` of the **actual** residual module (`S₀` the places above
  the charged primes, `M_{j+1} = Mcoef K S₀ E (j+1) χ₀`); it is transported to the genuine
  `genH K S₀ n` by `residualCohIso`, which uses `FullTorsion` at `2^{j+1}`, `2^j`, `2` and the
  trivial action on `E(K_{S₀})[2]`;
* the coefficient module of the support change (`transfer_final_genuine`) the **actual** residual
  module `ResidualM E j χ` of `M_{j+1} = Mcoef K S E (j+1) χ` over the smaller support `S` (its
  instance arguments, continuity of the action and finiteness, are discharged by
  `continuousSMul_residualM` and `finite_residualM` under the same hypotheses over `K_S`;
  Non-vacuity: `residualM_instances_cubicCurve`).

All other inputs are those of `residualRankCounts_genuine`. PROVED. -/
def residualRankCounts_actual (h410 : MilneADT_I_4_10_totallyComplex)
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
    -- the actual curve and coefficient module over `S₀`
    (E : WeierstrassCurve K) (j : ℕ)
    (χ₀ : GKS K (primesAboveSet K (chargedPrimes N r D)) →* (Acoef (j + 1))ˣ)
    (hT₀ : FullTorsion K (primesAboveSet K (chargedPrimes N r D)) E (2 ^ (j + 1)))
    (hM₀ : FullTorsion K (primesAboveSet K (chargedPrimes N r D)) E (2 ^ j))
    (h2₀ : FullTorsion K (primesAboveSet K (chargedPrimes N r D)) E 2)
    (htriv₀ : ∀ (σ : GKS K (primesAboveSet K (chargedPrimes N r D)))
      (P : TorsS K (primesAboveSet K (chargedPrimes N r D)) E ((2 : ℕ) : ℤ)), σ • P = P)
    -- the residual model and its identifications
    (Sloc : Set (HeightOneSpectrum (𝓞 K)))
    (Dsel : SelData (ZMod 2))
    [∀ n, Module.Finite (ZMod 2) (Dsel.G.X n)] [∀ n, Module.Finite (ZMod 2) (Dsel.U.X n)]
    [∀ n, Module.Finite (ZMod 2) (Dsel.L.X n)]
    (s : Finset ℤ) (hs : s ⊆ Finset.Icc 0 2)
    (eGact : ∀ n ∈ s, Dsel.G.X n ≃ₗ[ZMod 2]
      (letI := continuousSMul_residualM E j χ₀ hT₀ hM₀ h2₀ htriv₀
      contCohomology (ZMod 2) (GKS K (primesAboveSet K (chargedPrimes N r D)))
        (ResidualM E j χ₀) n.toNat))
    (hUm : ∑ n ∈ s, Module.finrank (ZMod 2) (Dsel.U.X n) ≤ ∑ p ∈ chargedPrimes N r D,
      condSum K (genCondDimFun2 K Sloc cond (kummerDimOfCurves K Ew (kd2OfCurves K Ew))) p)
    (hLm : ∑ n ∈ s, Module.finrank (ZMod 2) (Dsel.L.X (n - 1)) ≤
      ∑ p ∈ chargedPrimes N r D, genLocSum K Sloc p)
    -- the support change, with the actual residual module over `S`
    {S S' : Set (HeightOneSpectrum (𝓞 K))} (hSS' : S ⊆ S') (pr : ℕ)
    (hset : NekovarFiniteSetting K S pr (ZMod 2)) (hS' : S'.Finite)
    (χ : GKS K S →* (Acoef (j + 1))ˣ)
    [ContinuousSMul (GKS K S) (ResidualM E j χ)] [Finite (ResidualM E j χ)]
    (ψ : ∀ q : NewPlaces K S S', GUr K q.1 →ₜ* GKS K S)
    (hψ : ∀ (q : NewPlaces K S S') g, locMap K S q.1 g = ψ q (urRes K q.1 g))
    (Δ : GaloisLocalConditions K S (ZMod 2) (ResidualM E j χ))
    (Dfull : SelData (ZMod 2)) (W : GCx (ZMod 2))
    (f : GHom (galoisSupportData K hSS' (ZMod 2) (ResidualM E j χ) ψ hψ Δ).Dp.U Dfull.U)
    (g : GHom Dfull.U W)
    (hDp : (galoisSupportData K hSS' (ZMod 2) (ResidualM E j χ) ψ hψ Δ).Dp = restrictData Dfull f)
    (hfg : ∀ i (u : (galoisSupportData K hSS' (ZMod 2) (ResidualM E j χ) ψ hψ Δ).Dp.U.X i),
      g.f i i rfl (f.f i i rfl u) = 0)
    (hinj : ∀ i, Function.Injective (f.f i i rfl)) (hsurj : ∀ i, Function.Surjective (g.f i i rfl))
    (hex : ∀ i (u : Dfull.U.X i), g.f i i rfl u = 0 → ∃ u', f.f i i rfl u' = u)
    (hW : W.toCC.Acyclic) (a b : ℤ)
    [(selCx Dsel).toCC.IsStrictlyGE a] [(selCx Dsel).toCC.IsStrictlyLE b]
    (pP : (selCx Dsel).toCC ⟶
      (selCx (galoisSupportData K hSS' (ZMod 2) (ResidualM E j χ) ψ hψ Δ).D).toCC)
    [QuasiIso pP]
    (L : CochainComplex (ModuleCat.{0} (ZMod 2)) ℤ) [L.IsStrictlyGE a] [L.IsStrictlyLE b]
    [∀ i, Module.Finite (ZMod 2) (L.X i)]
    (hLmin : ∀ i j x, (L.d i j).hom x ∈
      IsLocalRing.maximalIdeal (ZMod 2) • (⊤ : Submodule (ZMod 2) (L.X j)))
    (pL : L ⟶ (selCx Dfull).toCC) [QuasiIso pL] :
    ResidualRankCounts :=
  residualRankCounts_genuine K Ew h410 h51 h28 h23 h788 k α hα hK N hN A hA r hr D hD hDodd cond
    hcondD hfull w hw Sloc Dsel s hs
    (fun n hn => (eGact n hn).trans
      (residualCohIso E j χ₀ hT₀ hM₀ h2₀ htriv₀ n.toNat).toLinearEquiv)
    hUm hLm hSS' pr hset hS' (ResidualM E j χ) ψ hψ Δ Dfull W f g hDp hfg hinj hsurj hex hW a b
    pP L hLmin pL

end Counts

end ZInQ.Contrib.CloudB3RC53.GenuineInst

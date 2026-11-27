import ZInQKernel.Contrib.OneProof.RC.Wiring.InnerLimitRegularityBounds
import ZInQKernel.Contrib.RC53Assist.LocalDegreeTwo.NormalizedPairing

/-!
# Theorem 5.3, Lane RC0 round 13: the split-stage pairing producer feeds the inner-limit switch

Lemma `ex:limits-inner-limit` (tex 4385–4451) at the stages `A_i`, with the split local model at
the derivative label (tex 4859–4873). The inner-limit switch (`ILStageStepActualB`) works over
the coefficient module `MinS hS W i α = InflMod hS (Mcoef K S₀ W i α)`: the module `M_i` of the
coefficient support `S₀`, inflated to `G_{K,S}` along the restriction `G_{K,S} → G_{K,S₀}`. The
split-stage pairing producer of the RC53 group (`exists_stagePairing_trace`) works over
`Mcoef K S W i α'` on the single Selmer support `S`, for a character `α'` of `G_{K,S}`.

**The transport** (PROVED here):
* `ksIncl`: the inclusion `K_{S₀} → K_S` of the maximal extensions unramified outside `S₀ ⊆ S`;
  `ksIncl_inflMap`: it intertwines `g ∈ G_{K,S}` and its restriction `inflMap g ∈ G_{K,S₀}`;
* `torsSIncl`: the induced map `E(K_{S₀})[N] → E(K_S)[N]`, injective (`torsSIncl_injective`) and
  equivariant along the restriction (`torsSIncl_smul`); it is bijective as soon as both
  `E(K_{S₀})[N]` and `E(K_S)[N]` have `N²` points (`FullTorsion` for `S₀` and for `S`,
  `torsSIncl_bijective`). Without the second hypothesis only the injective equivariant map is
  available: its bijectivity is exactly the statement that every `N`-torsion point over `K_S` is
  defined over `K_{S₀}`, which needs the bound `card E[N] ≤ N²` (not in the tree);
* `minsEquiv`: under the two full-torsion hypotheses, the `A_i`-linear equivalence
  `MinS hS W i α ≃ Mcoef K S W i (α ∘ inflMap)`, equivariant for `G_{K,S}` (`minsEquiv_smul`), hence
  for `G_{K_q}` acting through the localization at any `q` (`minsEquiv_smul_loc`);
* `stageLocalTransport`: the induced isomorphism of the local cochain complexes at `q`, from the
  stage local complex of the switch to the producer's `actualStageLocalCx W i (α ∘ inflMap) q`.

**The producer fed** (`exists_stagePairing_feed`, PROVED from the producer): at a positive stage,
with the old pair the switch's own Selmer data and its restriction to `q` followed by the
transport as the producer's restriction `rq` (the producer accepts any `rq`), the producer's
outputs give a comparison `cmp` of the switch's stage local complex with the split model and the
fields `Q`, `tr`, `htr`, `hdual` of the switch at that stage, over the switch's own localization
`ghomComp (stageRestrict …) cmp`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open CategoryTheory NumberField IsDedekindDomain WeierstrassCurve
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.RankCounts (unramifiedOutside unramifiedOutside_mono resAbs
  resAbs_surjective resAbs_apply_coe resUnr_comp)
open ZInQ.Manuscript.RC.CoefModules (KS galS TorsS Mcoef MinS InflMod CoefMod FullTorsion
  finite_torsS IsOpenKer)
open ZInQ.Manuscript.RC.SelmerComplex (GKS Gloc locMap ResMod inflMap contCochainsMap natHom)
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Contrib.CloudB3RC53.Duality (baseChangeAct baseChangeAct_tmul)
open scoped TensorProduct

/-! **The inclusion of the maximal extensions unramified outside `S₀ ⊆ S`** -/

section Fields

variable {K : Type} [Field K] [NumberField K] {S₀ S : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S)

/-- The inclusion `K_{S₀} → K_S`. Kind: definition. -/
abbrev ksIncl : KS K S₀ →ₐ[K] KS K S :=
  IntermediateField.inclusion (unramifiedOutside_mono K hS)

/-- **The inclusion intertwines `g ∈ G_{K,S}` and its restriction to `K_{S₀}`**. Kind: PROVED. -/
theorem ksIncl_inflMap (g : GKS K S) (x : KS K S₀) :
    ksIncl hS (galS K S₀ (inflMap K hS g) x) = galS K S g (ksIncl hS x) := by
  obtain ⟨σ, rfl⟩ := resAbs_surjective K S g
  have h : inflMap K hS (resAbs K S σ) = resAbs K S₀ σ := resUnr_comp K hS σ
  apply Subtype.ext
  have e1 : ((galS K S₀ (inflMap K hS (resAbs K S σ)) x : KS K S₀) : AlgebraicClosure K) =
      σ (x : AlgebraicClosure K) := by
    rw [h]
    exact resAbs_apply_coe K S₀ σ x
  have e2 : ((galS K S (resAbs K S σ) (ksIncl hS x) : KS K S) : AlgebraicClosure K) =
      σ (x : AlgebraicClosure K) := by
    have := resAbs_apply_coe K S σ (ksIncl hS x)
    rw [IntermediateField.coe_inclusion] at this
    exact this
  rw [IntermediateField.coe_inclusion, e1, e2]

theorem ksIncl_comp_inflMap (g : GKS K S) :
    (ksIncl hS).comp (galS K S₀ (inflMap K hS g)).toAlgHom =
      (galS K S g).toAlgHom.comp (ksIncl hS) :=
  AlgHom.ext fun x => ksIncl_inflMap hS g x

end Fields

/-! **The torsion points** -/

section Torsion

variable {K : Type} [Field K] [NumberField K] {S₀ S : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (W : WeierstrassCurve K) (N : ℤ)

/-- **`E(K_{S₀})[N] → E(K_S)[N]`**, the map of points along `K_{S₀} → K_S`. Kind: definition. -/
def torsSIncl : TorsS K S₀ W N →+ TorsS K S W N where
  toFun P := ⟨Affine.Point.map (ksIncl hS) P.1, by
    have hP : N • P.1 = 0 := (Submodule.mem_torsionBy_iff _ _).mp P.2
    change Affine.Point.map (ksIncl hS) P.1 ∈ Submodule.torsionBy ℤ _ N
    rw [Submodule.mem_torsionBy_iff, ← map_zsmul, hP, map_zero]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' P Q := Subtype.ext (map_add _ _ _)

omit [NumberField K] in
theorem torsSIncl_val (P : TorsS K S₀ W N) :
    (torsSIncl hS W N P).1 = Affine.Point.map (ksIncl hS) P.1 :=
  rfl

omit [NumberField K] in
/-- The map of torsion points is injective. Kind: PROVED. -/
theorem torsSIncl_injective : Function.Injective (torsSIncl hS W N) := by
  intro P Q h
  exact Subtype.ext (Affine.Point.map_injective (ksIncl hS) (congrArg Subtype.val h))

/-- **The map of torsion points is equivariant along the restriction** `G_{K,S} → G_{K,S₀}`.
Kind: PROVED. -/
theorem torsSIncl_smul (g : GKS K S) (P : TorsS K S₀ W N) :
    torsSIncl hS W N (inflMap K hS g • P) = g • torsSIncl hS W N P := by
  apply Subtype.ext
  change Affine.Point.map (ksIncl hS)
      (Affine.Point.map (galS K S₀ (inflMap K hS g)).toAlgHom P.1) =
    Affine.Point.map (galS K S g).toAlgHom (Affine.Point.map (ksIncl hS) P.1)
  rw [Affine.Point.map_map, Affine.Point.map_map, ksIncl_comp_inflMap]

omit [NumberField K] in
/-- **Bijectivity under full torsion over both supports**: an injective map between finite sets
of the same cardinality `N²`. Kind: PROVED. -/
theorem torsSIncl_bijective [W.IsElliptic] {n : ℕ} (hn : n ≠ 0) (hT0 : FullTorsion K S₀ W n)
    (hT : FullTorsion K S W n) : Function.Bijective (torsSIncl hS W (n : ℤ)) := by
  have : Finite (TorsS K S W (n : ℤ)) := finite_torsS (by exact_mod_cast hn)
  refine (torsSIncl_injective hS W (n : ℤ)).bijective_of_nat_card_le ?_
  unfold FullTorsion at hT0 hT
  rw [hT, hT0]

/-- The torsion points over `K_{S₀}` and over `K_S` under full torsion over both supports.
Kind: definition. -/
def torsSEquiv [W.IsElliptic] {n : ℕ} (hn : n ≠ 0) (hT0 : FullTorsion K S₀ W n)
    (hT : FullTorsion K S W n) : TorsS K S₀ W (n : ℤ) ≃+ TorsS K S W (n : ℤ) :=
  AddEquiv.ofBijective (torsSIncl hS W (n : ℤ)) (torsSIncl_bijective hS W hn hT0 hT)

omit [NumberField K] in
theorem torsSEquiv_apply [W.IsElliptic] {n : ℕ} (hn : n ≠ 0) (hT0 : FullTorsion K S₀ W n)
    (hT : FullTorsion K S W n) (P : TorsS K S₀ W (n : ℤ)) :
    torsSEquiv hS W hn hT0 hT P = torsSIncl hS W (n : ℤ) P :=
  rfl

end Torsion

/-! **The coefficient modules** -/

section Coefficients

variable {K : Type} [Field K] [NumberField K] {S₀ S : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ)
  (α : GKS K S₀ →* (Acoef i)ˣ)

/-- **The character of `G_{K,S}` inflated from `α`**: `α ∘ inflMap`. Kind: definition. -/
def inflChar : GKS K S →* (Acoef i)ˣ :=
  α.comp (inflMap K hS : GKS K S →* GKS K S₀)

theorem inflChar_apply (g : GKS K S) : inflChar hS i α g = α (inflMap K hS g) :=
  rfl

/-- The inflated character has an open kernel (the preimage of an open subgroup under the
continuous restriction). Kind: PROVED. -/
instance inflChar_isOpenKer [hα : IsOpenKer α] : IsOpenKer (inflChar hS i α) :=
  ⟨by
    change IsOpen ((inflMap K hS : GKS K S →* GKS K S₀) ⁻¹' (α.ker : Set (GKS K S₀)))
    exact hα.isOpen_ker.preimage (inflMap K hS).continuous⟩

/-- **`MinS hS W i α ≃ Mcoef K S W i (α ∘ inflMap)`**, under full `2^i`-torsion over `K_{S₀}`
and over `K_S`: the base change to `A_i` of the map of torsion points. Kind: definition. -/
def minsEquiv (hT0 : FullTorsion K S₀ W (2 ^ i)) (hT : FullTorsion K S W (2 ^ i)) :
    MinS hS W i α ≃ₗ[Acoef i] Mcoef K S W i (inflChar hS i α) :=
  LinearEquiv.baseChange ℤ (Acoef i) _ _
    (torsSEquiv hS W (pow_ne_zero i two_ne_zero) hT0 hT).toIntLinearEquiv

theorem minsEquiv_tmul (hT0 : FullTorsion K S₀ W (2 ^ i)) (hT : FullTorsion K S W (2 ^ i))
    (a : Acoef i) (P : TorsS K S₀ W ((2 ^ i : ℕ) : ℤ)) :
    minsEquiv hS W i α hT0 hT (show MinS hS W i α from a ⊗ₜ P) =
      (show Mcoef K S W i (inflChar hS i α) from a ⊗ₜ torsSIncl hS W _ P) :=
  rfl

/-- **The equivalence is equivariant for `G_{K,S}`** (acting on `MinS` through the restriction).
Kind: PROVED. -/
theorem minsEquiv_smul (hT0 : FullTorsion K S₀ W (2 ^ i)) (hT : FullTorsion K S W (2 ^ i))
    (g : GKS K S) (x : MinS hS W i α) :
    minsEquiv hS W i α hT0 hT (g • x) = g • minsEquiv hS W i α hT0 hT x := by
  induction x using TensorProduct.inductionOn with
  | tmul a P =>
    have e1 : (g • (show MinS hS W i α from a ⊗ₜ P) : MinS hS W i α) =
        (show MinS hS W i α from
          (((α (inflMap K hS g) : (Acoef i)ˣ) : Acoef i) * a) ⊗ₜ (inflMap K hS g • P)) :=
      CoefMod.smul_tmul (Acoef i) α _ (inflMap K hS g) a P
    have e2 : (g • (show Mcoef K S W i (inflChar hS i α) from a ⊗ₜ torsSIncl hS W _ P) :
          Mcoef K S W i (inflChar hS i α)) =
        (show Mcoef K S W i (inflChar hS i α) from
          (((inflChar hS i α g : (Acoef i)ˣ) : Acoef i) * a) ⊗ₜ (g • torsSIncl hS W _ P)) :=
      CoefMod.smul_tmul (Acoef i) (inflChar hS i α) _ g a _
    rw [e1, minsEquiv_tmul, minsEquiv_tmul, e2, torsSIncl_smul, inflChar_apply]
  | add x y hx hy =>
    change minsEquiv hS W i α hT0 hT
        (g • ((show MinS hS W i α from x) + (show MinS hS W i α from y))) =
      g • minsEquiv hS W i α hT0 hT ((show MinS hS W i α from x) + (show MinS hS W i α from y))
    rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- **The equivalence is equivariant for `G_{K_q}`** acting through the localization at any `q`.
Kind: PROVED. -/
theorem minsEquiv_smul_loc (hT0 : FullTorsion K S₀ W (2 ^ i)) (hT : FullTorsion K S W (2 ^ i))
    (q : HeightOneSpectrum (𝓞 K)) (h : Gloc K q) (x : ResMod (locMap K S q) (MinS hS W i α)) :
    (show ResMod (locMap K S q) (Mcoef K S W i (inflChar hS i α)) from
        minsEquiv hS W i α hT0 hT (h • x)) =
      h • (show ResMod (locMap K S q) (Mcoef K S W i (inflChar hS i α)) from
        minsEquiv hS W i α hT0 hT x) :=
  minsEquiv_smul hS W i α hT0 hT (locMap K S q h) x

end Coefficients

/-! **The local cochains at `q`, and the producer fed** -/

section Assoc

variable {A : Type} [CommRing A] {C₁ C₂ C₃ C₄ : GCx A}

/-- Composition of `GHom`s is associative. Kind: PROVED. -/
theorem ghomComp_assoc (f : GHom C₁ C₂) (g : GHom C₂ C₃) (h : GHom C₃ C₄) :
    ghomComp (ghomComp f g) h = ghomComp f (ghomComp g h) :=
  rfl

/-- Two `GHom`s with the same diagonal components are equal. Kind: PROVED. -/
theorem ghom_ext {f g : GHom C₁ C₂} (h : ∀ i (x : C₁.X i), f.f i i rfl x = g.f i i rfl x) :
    f = g := by
  cases f
  cases g
  congr
  funext i j hij
  subst hij
  exact LinearMap.ext (h i)

open ZInQ.Contrib.RC53Assist.InnerLimit (splitLocalComplex) in
open ZInQ.Manuscript.RC.FibreDuality (splitSelData) in
/-- The existence of a same-condition split Selmer pairing datum with a trace killing coboundaries
and a duality quasi-isomorphism, for given global data `G`, localization `r`, condition `U` and
condition map `ι` into the split local model. Kind: definition. -/
def SplitPairExists (G : GCx A) (r : GHom G (splitLocalComplex A)) (U : GCx A)
    (ι : GHom U (splitLocalComplex A)) : Prop :=
  ∃ (Q : SelPairData (splitSelData G r U ι) (splitSelData G r U ι))
    (tr : (coneCx Q.resE).X 3 →ₗ[A] A) (htr : ∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0),
    QuasiIso (GHom.toCC (globalDualityMap Q tr htr))

end Assoc

section Feed

open ZInQ.Contrib.RC53Assist.LocalDegreeTwo.SplitTrace (actualStageLocalCx
  exists_stagePairing_trace RetainedPlaceInput allTargetRes allPlacePair splitLocalRank)
open ZInQ.Contrib.RC53Assist.InnerLimit (splitLocalComplex)
open ZInQ.Manuscript.RC.FibreDuality (splitSelData)
open ZInQ.Manuscript.RC.SelmerComplex (contCochains natCx resCochains)
open ZInQ.Manuscript.RC.CoefModules (actualSelData CondAt)
open ZInQ.Manuscript.RC.SelmerComplex (Places)

variable {K : Type} [Field K] [NumberField K] {S₀ S : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) [NeZero i]
  (α : GKS K S₀ →* (Acoef i)ˣ) [IsOpenKer α]
  (hT0 : FullTorsion K S₀ W (2 ^ i)) (hT : FullTorsion K S W (2 ^ i))
  (q : HeightOneSpectrum (𝓞 K))

/-- **The isomorphism of the local cochain complexes at `q`**: from `C^•_cont(G_{K_q}, MinS)` (the
stage local complex of the switch) to the producer's `C^•_cont(G_{K_q}, Mcoef K S W i α')`,
`α' = α ∘ inflMap`, induced by `minsEquiv` (`contCochainsMap` along the identity of `G_{K_q}`).
Kind: definition (a chain map). -/
def stageLocalTransport :
    GHom (natCx (contCochains (Acoef i) (Gloc K q) (ResMod (locMap K S q) (MinS hS W i α))))
      (actualStageLocalCx W i (inflChar hS i α) q) :=
  natHom (contCochainsMap (ContinuousMonoidHom.id (Gloc K q))
    ((minsEquiv hS W i α hT0 hT).toLinearMap :
      ResMod (locMap K S q) (MinS hS W i α) →ₗ[Acoef i]
        ResMod (locMap K S q) (Mcoef K S W i (inflChar hS i α)))
    continuous_of_discreteTopology (fun h x => minsEquiv_smul_loc hS W i α hT0 hT q h x))

/-- **The producer's restriction for the switch**: restriction of the global cochains of the
switch's stage Selmer data to `q`, followed by the transport. The producer accepts any such
chain map `rq`. Kind: definition. -/
def switchRq (c : ∀ v : Places K S, v.1 ∈ S₀ → CondAt K S (Acoef i) (MinS hS W i α) v) :
    GHom (actualSelData hS W i α c).G (actualStageLocalCx W i (inflChar hS i α) q) :=
  ghomComp (natHom (resCochains (k := Acoef i) (M := MinS hS W i α) (locMap K S q)))
    (stageLocalTransport hS W i α hT0 hT q)

end Feed

section FeedFamily

open ZInQ.Contrib.RC53Assist.LocalDegreeTwo.SplitTrace (actualStageLocalCx
  exists_stagePairing_trace RetainedPlaceInput allTargetRes allPlacePair splitLocalRank)
open ZInQ.Contrib.RC53Assist.InnerLimit (splitLocalComplex)
open ZInQ.Manuscript.RC.FibreDuality (splitSelData)
open ZInQ.Manuscript.RC.CoefModules (actualSelData CondAt)
open ZInQ.Manuscript.RC.SelmerComplex (Places)

variable {K : Type} [Field K] [NumberField K] {S₀ S : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic]
  (α : ∀ j, GKS K S₀ →* (Acoef j)ˣ) [hα : ∀ j, IsOpenKer (α j)]
  (c : ∀ j, ∀ v : Places K S, v.1 ∈ S₀ → CondAt K S (Acoef j) (MinS hS W j (α j)) v)

/-- **The split-stage pairing producer fed into the inner-limit switch** (tex 4385–4451,
4859–4873), at a positive stage `i`: with the old pair the switch's own stage Selmer data
`actualSelData hS W i (α i) (c i)` and the producer's restriction the restriction to `q` followed by
the transport (`switchRq`), the producer's inputs give a comparison `p` of the producer's local
complex with the split model, and over the switch's own localization
`ghomComp (stageRestrict …) (ghomComp (stageLocalTransport …) p)` (the localization `actualRes`
of the switch at the stage, for the comparison `cmp i = ghomComp (stageLocalTransport …) p`) a
Selmer pairing datum `Q` with the condition `Uq` (map `ghomComp ιq p`), a trace `tr` killing
coboundaries, and the duality quasi-isomorphism. These are the fields `cmp`, `Uc`, `ιc`, `Q`, `tr`,
`htr`, `hdual` of `ILStageStepActualB` at the stage `i`. The producer's inputs (full torsion over
`K_S`, the derivative-prime conditions `h2`, `htriv`, `hμ`, the local finiteness and split ranks,
the retained same-condition cup data `Tq … V`, the trace `trAll`, and the global and local duality
quasi-isomorphisms `hG`, `hL` of the all-place pair) are hypotheses. Kind: PROVED (from the
producer). -/
theorem exists_stagePairing_feed (i : ℕ) [NeZero i] (hT0 : FullTorsion K S₀ W (2 ^ i))
    (hT : FullTorsion K S W (2 ^ i)) (q : HeightOneSpectrum (𝓞 K))
    (Qold : SelPairData (actualSelData hS W i (α i) (c i)) (actualSelData hS W i (α i) (c i)))
    (Tq Uq : GCx (Acoef i)) (sq : GHom Qold.E Tq)
    (ιq : GHom Uq (actualStageLocalCx W i (inflChar hS i (α i)) q))
    (Pq : GPair (actualStageLocalCx W i (inflChar hS i (α i)) q)
      (actualStageLocalCx W i (inflChar hS i (α i)) q) Tq)
    (V : RetainedPlaceInput (actualSelData hS W i (α i) (c i)) Qold
      (actualStageLocalCx W i (inflChar hS i (α i)) q) Tq Uq
      (switchRq hS W i (α i) hT0 hT q (c i)) sq ιq Pq)
    (trAll : (coneCx (allTargetRes (actualSelData hS W i (α i) (c i)) Qold Tq sq)).X 3 →ₗ[Acoef i]
      Acoef i)
    (htrAll : ∀ z, trAll ((coneCx (allTargetRes (actualSelData hS W i (α i) (c i)) Qold Tq
      sq)).d 2 3 rfl z) = 0)
    (h2 : (2 : 𝓞 K) ∉ q.asIdeal)
    (htriv : ∀ (g : Gloc K q)
      (m : ResMod (locMap K S q) (Mcoef K S W i (inflChar hS i (α i)))), g • m = m)
    (hμ : ∀ (g : Gal(AlgebraicClosure (q.adicCompletion K)/q.adicCompletion K))
      (ζ : AlgebraicClosure (q.adicCompletion K)), ζ ^ (2 ^ i) = 1 → g ζ = ζ)
    (hfin : ∀ n, Module.Finite (IsLocalRing.ResidueField (Acoef i))
      (ZInQ.Manuscript.RC.Limits.residualCohomologyAt
        (actualStageLocalCx W i (inflChar hS i (α i)) q) n))
    (hdim : ∀ n, Module.finrank (IsLocalRing.ResidueField (Acoef i))
      (ZInQ.Manuscript.RC.Limits.residualCohomologyAt
        (actualStageLocalCx W i (inflChar hS i (α i)) q) n) = splitLocalRank n)
    (hG : QuasiIso (GHom.toCC (globalDualityMap
      (allPlacePair (actualSelData hS W i (α i) (c i)) Qold
        (actualStageLocalCx W i (inflChar hS i (α i)) q) Tq Uq
        (switchRq hS W i (α i) hT0 hT q (c i)) sq ιq Pq V) trAll htrAll)))
    (hL : QuasiIso (GHom.toCC (localDualityMap
      (allPlacePair (actualSelData hS W i (α i) (c i)) Qold
        (actualStageLocalCx W i (inflChar hS i (α i)) q) Tq Uq
        (switchRq hS W i (α i) hT0 hT q (c i)) sq ιq Pq V) trAll htrAll))) :
    ∃ p : GHom (actualStageLocalCx W i (inflChar hS i (α i)) q) (splitLocalComplex (Acoef i)),
      SplitPairExists (selCx (actualSelData hS W i (α i) (c i)))
        (ghomComp (stageRestrict W (fun _ : ℕ => hS) α c i q)
          (ghomComp (stageLocalTransport hS W i (α i) hT0 hT q) p)) Uq (ghomComp ιq p) := by
  obtain ⟨p, Q, tr, htr, hdual⟩ := exists_stagePairing_trace W i (inflChar hS i (α i)) q
    (actualSelData hS W i (α i) (c i)) Qold Tq Uq (switchRq hS W i (α i) hT0 hT q (c i)) sq ιq Pq
    V trAll htrAll h2 hT htriv hμ hfin hdim hG hL
  have h1 : SplitPairExists (selCx (actualSelData hS W i (α i) (c i)))
      (ghomComp (ghomComp (projG (actualSelData hS W i (α i) (c i)))
        (switchRq hS W i (α i) hT0 hT q (c i))) p) Uq (ghomComp ιq p) := ⟨Q, tr, htr, hdual⟩
  have hloc : ghomComp (ghomComp (projG (actualSelData hS W i (α i) (c i)))
        (switchRq hS W i (α i) hT0 hT q (c i))) p =
      ghomComp (stageRestrict W (fun _ : ℕ => hS) α c i q)
        (ghomComp (stageLocalTransport hS W i (α i) hT0 hT q) p) := by
    exact ghom_ext fun n x => rfl
  rw [hloc] at h1
  exact ⟨p, h1⟩

end FeedFamily

end ZInQ.Manuscript.RC.Wiring

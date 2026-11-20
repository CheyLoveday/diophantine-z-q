import ZInQKernel.Contrib.OneProof.RC.Wiring.InnerLimitPairingFeed

/-!
# Theorem 5.3, Lane RC0 round 13: the degree-two coordinate of the fed comparison

The split-stage pairing producer of the RC53 group returns a comparison `p` of the actual local
cochains at the derivative label with the split model, as the projection of an oriented local
retract, and forgets the degree-two coordinate. The retract's `projection` field fixes `p` in
degree two: through the coefficient basis `e` it is the normalized coordinate `c₂`
(`orientedLocalRetraction_degreeTwo`), so the coordinate property of `c₂` transfers to `p`
(`exists_stagePairing_trace_coordinate`).

`LocalDegreeTwoCoordinate.transport` moves a degree-two coordinate along an equivariant isomorphism
of coefficient modules (through the induced isomorphism of continuous cochains). With
`minsEquiv`, the coordinate of the producer's comparison gives the field `hcmp` of the inner-limit
switch for the comparison `cmp = ghomComp (stageLocalTransport …) p` and the basis
`eM = minsEquiv ≪≫ e'` (`exists_stagePairing_feed_coordinate`).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open CategoryTheory NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Manuscript.RC.SelmerComplex (GKS Gloc locMap ResMod contCochains contCochainsMap natHom
  Places)
open ZInQ.Manuscript.RC.CoefModules (Mcoef MinS FullTorsion IsOpenKer actualSelData CondAt)
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Contrib.RC53Assist.InnerLimitArith (LocalDegreeTwoCoordinate)
open ZInQ.Contrib.RC53Assist.InnerLimit (Vec2 splitLocalComplex)

/-! **Transport of a degree-two coordinate along an equivariant isomorphism** -/

section Equivariant

variable {R : Type} [CommRing R] {G : Type} [Group G] {M N : Type} [AddCommGroup M] [Module R M]
  [DistribMulAction G M] [AddCommGroup N] [Module R N] [DistribMulAction G N]

/-- The inverse of an equivariant isomorphism is equivariant. Kind: PROVED. -/
theorem equivariant_symm (f : M ≃ₗ[R] N) (hf : ∀ (g : G) (m : M), f (g • m) = g • f m) (g : G)
    (n : N) : f.symm (g • n) = g • f.symm n := by
  apply f.injective
  rw [LinearEquiv.apply_symm_apply, hf, LinearEquiv.apply_symm_apply]

end Equivariant

section CochainComm

variable {R : Type} [CommRing R] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A morphism of continuous cochain complexes commutes with the differentials, elementwise.
Kind: PROVED. -/
theorem cochainHom_comm {P Q : Type} [AddCommGroup P] [Module R P] [DistribMulAction G P]
    [SMulCommClass G R P] [TopologicalSpace P] [ContinuousAdd P] [ContinuousConstSMul R P]
    [ContinuousSMul G P] [AddCommGroup Q] [Module R Q] [DistribMulAction G Q]
    [SMulCommClass G R Q] [TopologicalSpace Q] [ContinuousAdd Q] [ContinuousConstSMul R Q]
    [ContinuousSMul G Q] (T : contCochains R G P ⟶ contCochains R G Q) (i j : ℕ)
    (a : (contCochains R G P).X i) :
    (T.f j).hom (((contCochains R G P).d i j).hom a) =
      ((contCochains R G Q).d i j).hom ((T.f i).hom a) := by
  have h := congrArg (fun φ => ModuleCat.Hom.hom φ a) (T.comm i j)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h.symm

end CochainComm

section Transport

variable {R : Type} [CommRing R] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M N : Type} [AddCommGroup M] [Module R M] [DistribMulAction G M] [SMulCommClass G R M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]
  [AddCommGroup N] [Module R N] [DistribMulAction G N] [SMulCommClass G R N]
  [TopologicalSpace N] [DiscreteTopology N] [ContinuousSMul G N]
  (f : M ≃ₗ[R] N) (hf : ∀ (g : G) (m : M), f (g • m) = g • f m)

/-- The isomorphism of continuous cochains induced by an equivariant isomorphism of coefficient
modules. Kind: definition. -/
abbrev coefCochainsMap : contCochains R G M ⟶ contCochains R G N :=
  contCochainsMap (ContinuousMonoidHom.id G) f.toLinearMap continuous_of_discreteTopology
    (fun g m => hf g m)

theorem coefCochainsMap_left_inv (n : ℕ) (c : (contCochains R G M).X n) :
    ((coefCochainsMap f.symm (equivariant_symm f hf)).f n).hom
      (((coefCochainsMap f hf).f n).hom c) = c := by
  apply Subtype.ext
  funext x
  exact f.symm_apply_apply _

theorem coefCochainsMap_right_inv (n : ℕ) (c : (contCochains R G N).X n) :
    ((coefCochainsMap f hf).f n).hom
      (((coefCochainsMap f.symm (equivariant_symm f hf)).f n).hom c) = c := by
  apply Subtype.ext
  funext x
  exact f.apply_symm_apply _

/-- **A degree-two coordinate transports along an equivariant isomorphism**: if `c₂` is a
degree-two coordinate for `N`, then `f⁻¹ ∘ c₂ ∘ T₂` is one for `M`, where `T` is the induced
isomorphism of continuous cochains. Kind: PROVED. -/
theorem LocalDegreeTwoCoordinate.transport {c₂ : (contCochains R G N).X 2 →ₗ[R] N}
    (hc : LocalDegreeTwoCoordinate c₂) :
    LocalDegreeTwoCoordinate
      (f.symm.toLinearMap ∘ₗ c₂ ∘ₗ ((coefCochainsMap f hf).f 2).hom) := by
  obtain ⟨h1, h2, h3⟩ := hc
  refine ⟨fun a => ?_, fun z hz hcz => ?_, fun m => ?_⟩
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [cochainHom_comm, h1, map_zero]
  · have hz' : ((contCochains R G N).d 2 3).hom (((coefCochainsMap f hf).f 2).hom z) = 0 := by
      rw [← cochainHom_comm, hz, map_zero]
    have hcz' : c₂ (((coefCochainsMap f hf).f 2).hom z) = 0 := by
      have := congrArg f hcz
      simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
        map_zero] using this
    obtain ⟨b, hb⟩ := h2 _ hz' hcz'
    refine ⟨((coefCochainsMap f.symm (equivariant_symm f hf)).f 1).hom b, ?_⟩
    rw [← cochainHom_comm, hb, coefCochainsMap_left_inv]
  · obtain ⟨z', hz', hcz'⟩ := h3 (f m)
    refine ⟨((coefCochainsMap f.symm (equivariant_symm f hf)).f 2).hom z', ?_, ?_⟩
    · rw [← cochainHom_comm, hz', map_zero]
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [coefCochainsMap_right_inv, hcz', LinearEquiv.symm_apply_apply]

end Transport

/-! **The coordinate of the producer's comparison** -/

section Oriented

open ZInQ.Contrib.RC53Assist.LocalDegreeTwo.SplitTrace (OrientedLocalRetraction)

variable {A G M : Type} [CommRing A] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup M] [Module A M] [DistribMulAction G M] [SMulCommClass G A M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]
  (e : M ≃ₗ[A] Vec2 A) (φ σ : G) (c₂ : (contCochains A G M).X 2 →ₗ[A] M)

/-- **The degree-two part of an oriented retract's projection**, read through the inverse
coefficient basis, is the normalized degree-two coordinate (the retract's `projection` field in
degree two). Kind: PROVED. -/
theorem orientedLocalRetraction_degreeTwo (R : OrientedLocalRetraction e φ σ c₂) :
    e.symm.toLinearMap ∘ₗ R.retract.p.f 2 2 rfl = c₂ := by
  refine LinearMap.ext fun z => ?_
  change e.symm (R.retract.p.f 2 2 rfl z) = c₂ z
  rw [R.projection 2 z]
  exact e.symm_apply_apply (c₂ z)

/-- The coordinate property of `c₂` passes to the retract's projection. Kind: PROVED. -/
theorem orientedLocalRetraction_coordinate (R : OrientedLocalRetraction e φ σ c₂)
    (hc : LocalDegreeTwoCoordinate c₂) :
    LocalDegreeTwoCoordinate (e.symm.toLinearMap ∘ₗ R.retract.p.f 2 2 rfl) :=
  (congrArg (fun f => LocalDegreeTwoCoordinate (R := A) (G := G) (M := M) f)
    (orientedLocalRetraction_degreeTwo e φ σ c₂ R)).mpr hc

end Oriented

section ProducerCoordinate

open ZInQ.Contrib.RC53Assist.LocalDegreeTwo.SplitTrace (actualStageLocalCx RetainedPlaceInput
  allTargetRes allPlacePair splitLocalRank exists_stageOrientedLocalRetraction
  exists_relativeSplitPair_trace_duality)
open ZInQ.Manuscript.RC.FibreDuality (splitSelData)

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) [NeZero i]
  (α : GKS K S →* (Acoef i)ˣ) [IsOpenKer α] (q : HeightOneSpectrum (𝓞 K))
  (Dold : SelData (Acoef i)) (Qold : SelPairData Dold Dold) (Tq Uq : GCx (Acoef i))
  (rq : GHom Dold.G (actualStageLocalCx W i α q)) (sq : GHom Qold.E Tq)
  (ιq : GHom Uq (actualStageLocalCx W i α q))
  (Pq : GPair (actualStageLocalCx W i α q) (actualStageLocalCx W i α q) Tq)
  (V : RetainedPlaceInput Dold Qold (actualStageLocalCx W i α q) Tq Uq rq sq ιq Pq)
  (trAll : (coneCx (allTargetRes Dold Qold Tq sq)).X 3 →ₗ[Acoef i] Acoef i)
  (htrAll : ∀ z, trAll ((coneCx (allTargetRes Dold Qold Tq sq)).d 2 3 rfl z) = 0)

/-- **The split-stage pairing producer with the degree-two coordinate kept**: the RC53 group's
`exists_stageOrientedLocalRetraction` and `exists_relativeSplitPair_trace_duality` (the
combination of `exists_stagePairing_trace`), keeping the basis `e'` and the coordinate: the
degree-two part of the comparison `p`, read through `e'`, is a degree-two coordinate. Kind: PROVED
(from the producer's inputs). -/
theorem exists_stagePairing_trace_coordinate
    (h2 : (2 : 𝓞 K) ∉ q.asIdeal) (hW : FullTorsion K S W (2 ^ i))
    (htriv : ∀ (g : Gloc K q) (m : ResMod (locMap K S q) (Mcoef K S W i α)), g • m = m)
    (hμ : ∀ (g : Gal(AlgebraicClosure (q.adicCompletion K)/q.adicCompletion K))
      (ζ : AlgebraicClosure (q.adicCompletion K)), ζ ^ (2 ^ i) = 1 → g ζ = ζ)
    (hfin : ∀ n, Module.Finite (IsLocalRing.ResidueField (Acoef i))
      (ZInQ.Manuscript.RC.Limits.residualCohomologyAt (actualStageLocalCx W i α q) n))
    (hdim : ∀ n, Module.finrank (IsLocalRing.ResidueField (Acoef i))
      (ZInQ.Manuscript.RC.Limits.residualCohomologyAt (actualStageLocalCx W i α q) n) =
        splitLocalRank n)
    (hG : QuasiIso (GHom.toCC (globalDualityMap
      (allPlacePair Dold Qold (actualStageLocalCx W i α q) Tq Uq rq sq ιq Pq V) trAll htrAll)))
    (hL : QuasiIso (GHom.toCC (localDualityMap
      (allPlacePair Dold Qold (actualStageLocalCx W i α q) Tq Uq rq sq ιq Pq V) trAll htrAll))) :
    ∃ (e' : ResMod (locMap K S q) (Mcoef K S W i α) ≃ₗ[Acoef i] Vec2 (Acoef i))
      (p : GHom (actualStageLocalCx W i α q) (splitLocalComplex (Acoef i))),
      LocalDegreeTwoCoordinate (R := Acoef i) (G := Gloc K q)
        (M := ResMod (locMap K S q) (Mcoef K S W i α)) (e'.symm.toLinearMap ∘ₗ p.f 2 2 rfl) ∧
      SplitPairExists (selCx Dold) (ghomComp (ghomComp (projG Dold) rq) p) Uq (ghomComp ιq p) := by
  obtain ⟨D, c₂, η, e, R, hc, -⟩ := exists_stageOrientedLocalRetraction (K := K) (S := S)
    W i α q h2 hW htriv hμ hfin hdim
  obtain ⟨Q, tr, htr, hdual, -⟩ :=
    exists_relativeSplitPair_trace_duality Dold Qold (actualStageLocalCx W i α q)
      Tq Uq rq sq ιq Pq V trAll htrAll R.retract hG hL
  exact ⟨e, R.retract.p,
    orientedLocalRetraction_coordinate (G := Gloc K q) e D.frobenius D.inertia c₂ R hc,
    Q, tr, htr, hdual⟩

end ProducerCoordinate

/-! **The fed comparison of the inner-limit switch with its degree-two coordinate** -/

section FeedCoordinate

open ZInQ.Contrib.RC53Assist.LocalDegreeTwo.SplitTrace (actualStageLocalCx RetainedPlaceInput
  allTargetRes allPlacePair splitLocalRank)

variable {K : Type} [Field K] [NumberField K] {S₀ S : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic]
  (α : ∀ j, GKS K S₀ →* (Acoef j)ˣ) [hα : ∀ j, IsOpenKer (α j)]
  (c : ∀ j, ∀ v : Places K S, v.1 ∈ S₀ → CondAt K S (Acoef j) (MinS hS W j (α j)) v)

/-- **The split-stage pairing producer fed into the inner-limit switch, with the degree-two
coordinate** (tex 4385–4451, 4859–4873), at a positive stage `i`: from the producer's inputs (as
in `exists_stagePairing_feed`), a basis `eM` of the switch's local coefficient module `MinS` and a
comparison `p` such that, for `cmp = ghomComp (stageLocalTransport …) p`, the degree-two part of
`cmp` read through `eM` is a degree-two coordinate (the field `hcmp` of `ILStageStepActualB`), and
the same-condition split Selmer pairing datum, trace and duality quasi-isomorphism exist over the
switch's own localization (the fields `Q`, `tr`, `htr`, `hdual`). The basis is
`eM = minsEquiv ≪≫ e'`, with `e'` the producer's basis, and the coordinate is transported along
`minsEquiv` (`LocalDegreeTwoCoordinate.transport`). Kind: PROVED (from the producer's inputs). -/
theorem exists_stagePairing_feed_coordinate (i : ℕ) [NeZero i] (hT0 : FullTorsion K S₀ W (2 ^ i))
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
    ∃ (eM : ResMod (locMap K S q) (MinS hS W i (α i)) ≃ₗ[Acoef i] Vec2 (Acoef i))
      (p : GHom (actualStageLocalCx W i (inflChar hS i (α i)) q) (splitLocalComplex (Acoef i))),
      LocalDegreeTwoCoordinate (R := Acoef i) (G := Gloc K q)
        (M := ResMod (locMap K S q) (MinS hS W i (α i)))
        (eM.symm.toLinearMap ∘ₗ
          (ghomComp (stageLocalTransport hS W i (α i) hT0 hT q) p).f 2 2 rfl) ∧
      SplitPairExists (selCx (actualSelData hS W i (α i) (c i)))
        (ghomComp (stageRestrict W (fun _ : ℕ => hS) α c i q)
          (ghomComp (stageLocalTransport hS W i (α i) hT0 hT q) p)) Uq (ghomComp ιq p) := by
  obtain ⟨e', p, hcoord, h1⟩ := exists_stagePairing_trace_coordinate W i (inflChar hS i (α i)) q
    (actualSelData hS W i (α i) (c i)) Qold Tq Uq (switchRq hS W i (α i) hT0 hT q (c i)) sq ιq Pq
    V trAll htrAll h2 hT htriv hμ hfin hdim hG hL
  let f : ResMod (locMap K S q) (MinS hS W i (α i)) ≃ₗ[Acoef i]
      ResMod (locMap K S q) (Mcoef K S W i (inflChar hS i (α i))) :=
    minsEquiv hS W i (α i) hT0 hT
  have hf : ∀ (g : Gloc K q) (m : ResMod (locMap K S q) (MinS hS W i (α i))),
      f (g • m) = g • f m := fun g m => minsEquiv_smul_loc hS W i (α i) hT0 hT q g m
  have key := LocalDegreeTwoCoordinate.transport (G := Gloc K q) f hf hcoord
  refine ⟨f.trans e', p, ?_, ?_⟩
  · have heq : (f.trans e').symm.toLinearMap ∘ₗ
          (ghomComp (stageLocalTransport hS W i (α i) hT0 hT q) p).f 2 2 rfl =
        f.symm.toLinearMap ∘ₗ (e'.symm.toLinearMap ∘ₗ p.f 2 2 rfl) ∘ₗ
          ((coefCochainsMap f hf).f 2).hom :=
      LinearMap.ext fun z => rfl
    exact (congrArg (fun g => LocalDegreeTwoCoordinate (R := Acoef i) (G := Gloc K q)
      (M := ResMod (locMap K S q) (MinS hS W i (α i))) g) heq).mpr key
  · have hloc : ghomComp (ghomComp (projG (actualSelData hS W i (α i) (c i)))
          (switchRq hS W i (α i) hT0 hT q (c i))) p =
        ghomComp (stageRestrict W (fun _ : ℕ => hS) α c i q)
          (ghomComp (stageLocalTransport hS W i (α i) hT0 hT q) p) :=
      ghom_ext fun n x => rfl
    rw [hloc] at h1
    exact h1

end FeedCoordinate

end ZInQ.Manuscript.RC.Wiring

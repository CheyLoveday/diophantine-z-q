
/-! # Part C: the reciprocity clause applies to every `σ ∈ Aut(ℂ/κ(K))`

C1 (verbatim copies from origin/wip/t5-glue, `scratch/t5-glue/`): `mem_range_of_isAlgebraic`
(`Field.lean`), `AbsArtinSurjective` (`parts/Artin.lean`) and the section `AbsArtin` of
`parts/AbsArtin.lean` (surjectivity of Tau Ceti's absolute Artin map for number fields without real
places, proved). C2 (new): every `σ ∈ Aut(ℂ)` fixing `κ(K)` is `[s, K]` on `K^ab` for some idele `s`
(`exists_artinCondC`), so clause 4 of `ShimuraDeligneBody` determines `σ(Ψ(z, g))` for all such `σ`. -/

noncomputable section

namespace T5Glue

open MvPolynomial

/-- An element algebraic over an algebraically closed subfield lies in it. -/
theorem mem_range_of_isAlgebraic {k K : Type*} [Field k] [IsAlgClosed k] [Field K] [Algebra k K]
    {z : K} (hz : IsAlgebraic k z) : z ∈ Set.range (algebraMap k K) := by
  have hi : IsIntegral k z := hz.isIntegral
  exact minpoly.mem_range_of_degree_eq_one k z
    (IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hi))

end T5Glue


noncomputable section

set_option maxRecDepth 20000

namespace T5Glue

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.RingClass
  ZInQ.RouteK.Rank5b NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory Complex
  ZInQ.Contrib.TYZGenus.Shimura IsDedekindDomain

/-- **GLUE ABS-ARTIN-SURJ (class field theory, over Tau Ceti's own objects).** The absolute Artin
map `C_K → G_K^ab` of Tau Ceti's global class formation is surjective: every element of the
absolute Galois group is, modulo the closure of the commutator subgroup, the absolute Artin symbol
of an idele class. (Tau Ceti proves dense image, `ClassFormation.denseRange_absoluteArtinMap`;
surjectivity for number fields follows from the compactness of `C_K` modulo its connected component
(finite class number, compactness of `Ô^×`, Artin symbols trivial on the archimedean component):
Neukirch, *Algebraic number theory*, VI.5; Artin–Tate, Ch. IX; UNVERIFIED numbers.) -/
def AbsArtinSurjective (K : Type) [Field K] [NumberField K] : Prop :=
  ∀ g : TauCeti.AbsoluteGaloisGroup K, ∃ c : IdeleClassGroup (𝓞 K) K,
    Additive.ofMul (g : TopologicalAbelianization (TauCeti.AbsoluteGaloisGroup K)) =
      (globalClassFormation K).absoluteArtinMap (globalGroundEquiv K (Additive.ofMul c))

section AbsArtin

variable (K : Type) [Field K] [NumberField K]

set_option synthInstance.maxHeartbeats 400000 in
instance zeroDim_Gab :
    ZeroDimensionalSpace (TopologicalAbelianization (TauCeti.AbsoluteGaloisGroup K)) :=
  inferInstance

/-- The absolute Artin map `C_K →* G_K^ab` (multiplicative form). -/
def absArt : IdeleClassGroup (𝓞 K) K →* TopologicalAbelianization (TauCeti.AbsoluteGaloisGroup K) :=
  MonoidHom.toAdditive.symm
    ((globalClassFormation K).absoluteArtinMap.comp (globalGroundEquiv K).toAddMonoidHom)

theorem ofMul_absArt (c : IdeleClassGroup (𝓞 K) K) :
    Additive.ofMul (absArt K c) =
      (globalClassFormation K).absoluteArtinMap (globalGroundEquiv K (Additive.ofMul c)) :=
  rfl

theorem continuous_absArt : Continuous (absArt K) := by
  refine continuous_of_continuousAt_one (absArt K) ?_
  rw [ContinuousAt, map_one]
  intro N hN
  obtain ⟨U0, hU0N, hU0o, h1⟩ := mem_nhds_iff.1 hN
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hU0o h1
  obtain ⟨V, hV⟩ := (globalClassFormation K).exists_absoluteArtinMap_mem_iff H.toOpenSubgroup
  have hpre : ∀ c, c ∈ globalNormSubgroup K V → absArt K c ∈ (H : Set _) := by
    intro c hc
    rw [mem_globalNormSubgroup_iff, ← hV] at hc
    exact hc
  rw [Filter.mem_map]
  refine Filter.mem_of_superset ((isOpen_globalNormSubgroup K V).mem_nhds (one_mem _)) ?_
  intro c hc
  exact hU0N (hH (hpre c hc))

theorem denseRange_absArt : DenseRange (absArt K) := by
  have h1 : DenseRange (fun a => Additive.toMul ((globalClassFormation K).absoluteArtinMap a)) :=
    DenseRange.comp (Additive.toMul.surjective.denseRange) (globalClassFormation K).denseRange_absoluteArtinMap
      continuous_toMul
  have h2 : Function.Surjective fun c : IdeleClassGroup (𝓞 K) K =>
      globalGroundEquiv K (Additive.ofMul c) :=
    (globalGroundEquiv K).surjective.comp Additive.ofMul.surjective
  have : (absArt K : IdeleClassGroup (𝓞 K) K → _) =
      (fun a => Additive.toMul ((globalClassFormation K).absoluteArtinMap a)) ∘
        (fun c : IdeleClassGroup (𝓞 K) K => globalGroundEquiv K (Additive.ofMul c)) := rfl
  rw [DenseRange, this, h2.range_comp]
  exact h1

/-- **Idele classes with trivial finite part are killed** (no real places). -/
theorem absArt_eq_one_of_coord (hK : ∀ w : InfinitePlace K, ¬ w.IsReal) (x : IdeleGroup (𝓞 K) K)
    (hx : ∀ v : HeightOneSpectrum (𝓞 K), v.ideleFiniteCoord x = 1) :
    absArt K (x : IdeleClassGroup (𝓞 K) K) = 1 := by
  apply Additive.ofMul.injective
  rw [ofMul_absArt, ofMul_one, (globalClassFormation K).absoluteArtinMap_eq_zero_iff]
  intro V
  have hmem : (x : IdeleClassGroup (𝓞 K) K) ∈ globalNormSubgroup K V := by
    rw [globalNormSubgroup_eq_range_classField]
    apply isAdmissibleModulus_abelianConductor K (classField K V)
    rw [mem_raySubgroup_iff]
    refine ⟨x, ?_, rfl⟩
    rw [mem_ideleCongruenceSubgroup_iff]
    refine ⟨fun v _ => by simp [hx v], fun v _ => by simp [hx v], fun w _ => absurd w.2 (hK w.1)⟩
  exact hmem

/-- Units of the integral finite adeles, `Ô^×`. -/
def intUnits : Set (FiniteAdeleRing (𝓞 K) K)ˣ :=
  {w | (w : FiniteAdeleRing (𝓞 K) K) ∈ FiniteAdeleRing.integralAdeles (𝓞 K) K ∧
    ((w⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) ∈
      FiniteAdeleRing.integralAdeles (𝓞 K) K}

theorem isCompact_intUnits : IsCompact (intUnits K) := by
  have hc := FiniteAdeleRing.isCompact_integralAdeles (R := 𝓞 K) (K := K)
  have hc2 : IsCompact ((FiniteAdeleRing.integralAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)) ×ˢ
      (MulOpposite.op '' (FiniteAdeleRing.integralAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)))) :=
    hc.prod (hc.image MulOpposite.continuous_op)
  have := Units.isClosedEmbedding_embedProduct.isCompact_preimage hc2
  convert this using 1
  ext w
  simp [intUnits, Units.embedProduct]

/-- `Ô^× → 𝕀_K`, `w ↦ (1, w)`. -/
def finEmb : (FiniteAdeleRing (𝓞 K) K)ˣ →* IdeleGroup (𝓞 K) K :=
  Units.map (MonoidHom.inr (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) :
    FiniteAdeleRing (𝓞 K) K →* AdeleRing (𝓞 K) K)

theorem continuous_finEmb : Continuous (finEmb K) :=
  Units.continuous_map (show Continuous fun w : FiniteAdeleRing (𝓞 K) K =>
    ((1 : InfiniteAdeleRing K), w) from continuous_const.prodMk continuous_id)

/-- The compact set `T = ⋃_q q̄·[Ô^×]` (finitely many ray-class representatives `q̄`). -/
def bigT : Set (IdeleClassGroup (𝓞 K) K) :=
  ⋃ q : IdeleClassGroup (𝓞 K) K ⧸ raySubgroup (Modulus.one K),
    (fun w => q.out * ((finEmb K w : IdeleGroup (𝓞 K) K) : IdeleClassGroup (𝓞 K) K)) '' intUnits K

theorem isCompact_bigT : IsCompact (bigT K) := by
  have : Finite (IdeleClassGroup (𝓞 K) K ⧸ raySubgroup (Modulus.one K)) :=
    Subgroup.finite_quotient_of_finiteIndex
  refine isCompact_iUnion fun q => (isCompact_intUnits K).image ?_
  have hmk : Continuous (QuotientGroup.mk : IdeleGroup (𝓞 K) K → IdeleClassGroup (𝓞 K) K) :=
    QuotientGroup.continuous_mk
  exact continuous_const.mul (hmk.comp (continuous_finEmb K))

theorem range_absArt_eq (hK : ∀ w : InfinitePlace K, ¬ w.IsReal) :
    Set.range (absArt K) = absArt K '' bigT K := by
  refine Set.Subset.antisymm ?_ (Set.image_subset_range _ _)
  rintro _ ⟨c, rfl⟩
  set q : IdeleClassGroup (𝓞 K) K ⧸ raySubgroup (Modulus.one K) := QuotientGroup.mk c
  obtain ⟨⟨h, hh⟩, hq⟩ := QuotientGroup.mk_out_eq_mul (raySubgroup (Modulus.one K)) c
  -- `c = q̄ · h⁻¹` with `h⁻¹` a ray class
  have hc : c = q.out * h⁻¹ := by rw [hq, mul_inv_cancel_right]
  obtain ⟨x, hx, hxc⟩ := mem_raySubgroup_iff.1 (inv_mem hh)
  rw [mem_ideleCongruenceSubgroup_iff] at hx
  have hv1 : ∀ v : HeightOneSpectrum (𝓞 K),
      Valued.v (v.ideleFiniteCoord x : v.adicCompletion K) = 1 := by
    intro v
    refine hx.1 v ?_
    intro hdvd
    have : (Modulus.one K).finitePart = ⊤ := rfl
    rw [this, Ideal.dvd_iff_le, top_le_iff] at hdvd
    exact v.isPrime.ne_top hdvd
  set xf := IdeleGroup.toFiniteIdele (𝓞 K) K x
  have hcoord : ∀ v : HeightOneSpectrum (𝓞 K),
      ((xf : FiniteAdeleRing (𝓞 K) K) v) = (v.ideleFiniteCoord x : v.adicCompletion K) := fun v => rfl
  have hcoordi : ∀ v : HeightOneSpectrum (𝓞 K),
      ((xf⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v =
        ((v.ideleFiniteCoord x)⁻¹ : (v.adicCompletion K)ˣ) := fun v => rfl
  have hxf : xf ∈ intUnits K := by
    refine ⟨fun v => ?_, fun v => ?_⟩
    · rw [hcoord, HeightOneSpectrum.mem_adicCompletionIntegers, hv1 v]
    · rw [hcoordi, HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, map_inv₀,
        hv1 v, inv_one]
  set y := (finEmb K xf)⁻¹ * x
  have hy : ∀ v : HeightOneSpectrum (𝓞 K), v.ideleFiniteCoord y = 1 := by
    intro v
    apply Units.ext
    show ((finEmb K xf)⁻¹ * x : IdeleGroup (𝓞 K) K).val.2 v = 1
    rw [Units.val_mul, Prod.snd_mul]
    show ((xf⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v * (x.val.2 v) = 1
    have e1 : ((xf⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) * xf = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have e2 : ((xf⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v *
        (xf : FiniteAdeleRing (𝓞 K) K) v = 1 := by
      rw [← FiniteAdeleRing.mul_apply, e1, FiniteAdeleRing.one_apply]
    exact e2
  have hxy : x = finEmb K xf * y := by rw [mul_inv_cancel_left]
  refine ⟨q.out * ((finEmb K xf : IdeleGroup (𝓞 K) K) : IdeleClassGroup (𝓞 K) K),
    Set.mem_iUnion.2 ⟨q, xf, hxf, rfl⟩, ?_⟩
  rw [hc, ← hxc, QuotientGroup.mk'_apply, hxy, QuotientGroup.mk_mul, map_mul, map_mul, map_mul,
    absArt_eq_one_of_coord K hK y hy, mul_one]

/-- **`AbsArtinSurjective K` for number fields without real places.** -/
theorem absArtinSurjective_of_noReal (hK : ∀ w : InfinitePlace K, ¬ w.IsReal) :
    AbsArtinSurjective K := by
  have hclosed : IsClosed (Set.range (absArt K)) := by
    rw [range_absArt_eq K hK]
    exact ((isCompact_bigT K).image (continuous_absArt K)).isClosed
  intro g
  have hg : (g : TopologicalAbelianization (TauCeti.AbsoluteGaloisGroup K)) ∈ Set.range (absArt K) := by
    rw [← hclosed.closure_eq]
    exact denseRange_absArt K _
  obtain ⟨c, hc⟩ := hg
  exact ⟨c, by rw [← ofMul_absArt, hc]⟩

end AbsArtin

end T5Glue

namespace ShimuraCFT

open NumberField TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields

variable {K : Type} [Field K] [NumberField K]

/-- `σ ∈ Aut(ℂ)` fixing `κ(K)` acts on `e(Kˢ)` through some `τ ∈ Gal(Kˢ/K)`, for a `K`-embedding
`e : Kˢ → ℂ` (generalizes t5-glue's `exists_tau_of_sigma`). -/
theorem exists_tau (κ : K →+* ℂ) (e : SeparableClosure K →+* ℂ)
    (he : e.comp (algebraMap K (SeparableClosure K)) = κ) (σ : ℂ ≃+* ℂ)
    (hσ : ∀ k : K, σ (κ k) = κ k) :
    ∃ τ : TauCeti.AbsoluteGaloisGroup K, ∀ x, σ (e x) = e (τ x) := by
  set Ks := SeparableClosure K
  have hεinj : Function.Injective e := e.injective
  letI : Algebra Ks ℂ := e.toAlgebra
  have halgK : Algebra.IsAlgebraic ℚ Ks := Algebra.IsAlgebraic.trans ℚ K Ks
  have hrange : ∀ z : ℂ, IsAlgebraic ℚ z → ∃ y : Ks, e y = z := by
    intro z hz
    have hz' : IsAlgebraic Ks z := hz.extendScalars (algebraMap ℚ Ks).injective
    obtain ⟨y, hy⟩ := T5Glue.mem_range_of_isAlgebraic hz'
    exact ⟨y, hy⟩
  have halg : ∀ (φ : ℂ ≃+* ℂ) (x : Ks), IsAlgebraic ℚ (φ (e x)) := by
    intro φ x
    have h1 : IsAlgebraic ℚ (e x) := (halgK.isAlgebraic x).algHom (e.toRatAlgHom)
    exact h1.algHom ((φ : ℂ →+* ℂ).toRatAlgHom)
  choose τf hτf using fun x => hrange (σ (e x)) (halg σ x)
  choose τi hτi using fun x => hrange (σ.symm (e x)) (halg σ.symm x)
  have hK : ∀ k : K, e (algebraMap K Ks k) = κ k := fun k => by rw [← he]; rfl
  let τh : Ks →ₐ[K] Ks :=
    { toFun := τf
      map_one' := hεinj (by simp [hτf])
      map_mul' := fun x y => hεinj (by rw [hτf, map_mul, map_mul, map_mul, hτf, hτf])
      map_zero' := hεinj (by simp [hτf])
      map_add' := fun x y => hεinj (by rw [hτf, map_add, map_add, map_add, hτf, hτf])
      commutes' := fun k => hεinj (by
        show e (τf (algebraMap K Ks k)) = e (algebraMap K Ks k)
        rw [hτf, hK, hσ]) }
  have hbij : Function.Bijective τh := by
    refine ⟨fun x y hxy => ?_, fun y => ⟨τi y, ?_⟩⟩
    · have h := congrArg e hxy
      change e (τf x) = e (τf y) at h
      rw [hτf, hτf] at h
      exact hεinj (σ.injective h)
    · apply hεinj
      change e (τf (τi y)) = e y
      rw [hτf, hτi, RingEquiv.apply_symm_apply]
  refine ⟨AlgEquiv.ofBijective τh hbij, fun x => ?_⟩
  show σ (e x) = e (τf x)
  rw [hτf]

/-- A `K`-embedding `j : L → ℂ` of a finite extension factors through `e : Kˢ → ℂ`. -/
theorem exists_iota (κ : K →+* ℂ) (e : SeparableClosure K →+* ℂ)
    (he : e.comp (algebraMap K (SeparableClosure K)) = κ)
    (L : Type) [Field L] [NumberField L] [Algebra K L] (j : L →+* ℂ)
    (hj : j.comp (algebraMap K L) = κ) :
    ∃ ι : L →ₐ[K] SeparableClosure K, ∀ x, e (ι x) = j x := by
  set Ks := SeparableClosure K
  have hεinj : Function.Injective e := e.injective
  letI : Algebra Ks ℂ := e.toAlgebra
  have hrange : ∀ z : ℂ, IsAlgebraic ℚ z → ∃ y : Ks, e y = z := by
    intro z hz
    have hz' : IsAlgebraic Ks z := hz.extendScalars (algebraMap ℚ Ks).injective
    obtain ⟨y, hy⟩ := T5Glue.mem_range_of_isAlgebraic hz'
    exact ⟨y, hy⟩
  have halg : ∀ x : L, IsAlgebraic ℚ (j x) := fun x =>
    ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x)).algHom (j.toRatAlgHom)
  choose ιf hιf using fun x => hrange (j x) (halg x)
  have hK : ∀ k : K, e (algebraMap K Ks k) = κ k := fun k => by rw [← he]; rfl
  have hK' : ∀ k : K, j (algebraMap K L k) = κ k := fun k => by rw [← hj]; rfl
  refine ⟨{ toFun := ιf
            map_one' := hεinj (by simp [hιf])
            map_mul' := fun x y => hεinj (by rw [hιf, map_mul, map_mul, hιf, hιf])
            map_zero' := hεinj (by simp [hιf])
            map_add' := fun x y => hεinj (by rw [hιf, map_add, map_add, hιf, hιf])
            commutes' := fun k => hεinj (by
              show e (ιf (algebraMap K L k)) = e (algebraMap K Ks k)
              rw [hιf, hK, hK']) }, fun x => hιf x⟩

open scoped IsMulCommutative in
/-- **Every `σ ∈ Aut(ℂ)` fixing `κ(K)` is `[s, K]` on `K^ab`** (`ArtinCondC`), when Tau Ceti's absolute
Artin map of `K` is surjective. -/
theorem exists_artinCondC_of_abs (hA : T5Glue.AbsArtinSurjective K) (κ : K →+* ℂ) (σ : ℂ ≃+* ℂ)
    (hσ : ∀ k : K, σ (κ k) = κ k) : ∃ s : IdeleGroup (𝓞 K) K, ArtinCondC κ σ s := by
  letI : Algebra K ℂ := κ.toAlgebra
  let e : SeparableClosure K →ₐ[K] ℂ := IsAlgClosed.lift
  have he : (e : SeparableClosure K →+* ℂ).comp (algebraMap K (SeparableClosure K)) = κ := by
    ext k; exact e.commutes k
  obtain ⟨τ, hτ⟩ := exists_tau κ (e : SeparableClosure K →+* ℂ) he σ hσ
  obtain ⟨c, hc⟩ := hA τ
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective c
  refine ⟨s, ?_⟩
  intro L _ _ _ _ j hj x
  obtain ⟨ι, hι⟩ := exists_iota κ (e : SeparableClosure K →+* ℂ) he L j hj
  have h1 := of_ideleClassArtinMap K L ι (QuotientGroup.mk s)
  have h0 := globalArtinMap_eq_of_mk_eq_absoluteArtinMap K L ι τ hc
  have h3 : Abelianization.of (ideleClassArtinMap K L (QuotientGroup.mk s)) =
      Abelianization.of (ι.restrictNormalHom τ) := by
    rw [h1, h0, toMul_ofMul]
  have h2 : ideleClassArtinMap K L (QuotientGroup.mk s) = ι.restrictNormalHom τ :=
    (Abelianization.equivOfComm (H := Gal(L/K))).injective h3
  rw [h2, ← hι, ← hι, AlgHom.restrictNormalHom_commutes]
  exact hτ (ι x)

/-- **Every `σ ∈ Aut(ℂ)` fixing `κ(K)` is `[s, K]` on `K^ab`** for `K` totally complex (in particular
imaginary quadratic), from t5-glue's proved surjectivity of the absolute Artin map. -/
theorem exists_artinCondC [IsTotallyComplex K] (κ : K →+* ℂ) (σ : ℂ ≃+* ℂ)
    (hσ : ∀ k : K, σ (κ k) = κ k) : ∃ s : IdeleGroup (𝓞 K) K, ArtinCondC κ σ s :=
  exists_artinCondC_of_abs (T5Glue.absArtinSurjective_of_noReal K fun w hw =>
    (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)) hw) κ σ hσ

end ShimuraCFT

#print axioms ShimuraCFT.exists_artinCondC

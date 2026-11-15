import ZInQKernel.Contrib.OneProof.FaltingsLemma5Lower.Cot

/-! faltings5-lower, part 10: a derivation of `𝒪_{𝒢,ξ}` at the origin killing `𝓞_K` and
`f^*(𝒪_{𝒩,ξ})` vanishes (tangent vectors of `A` killed by an isogeny are trivial: Milne's
quasi-inverse and `ZInQ.Contrib.AbVarBC.Tangent.eq_one_of_comp_intCast`). -/

set_option linter.style.haveILetI false

namespace GapHeight

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings ZInQ.Contrib.AbVarBC.Tangent TrivSqZeroExt

section Tan

variable {K : Type} [Field K] [NumberField K] {A B : PkgI3.AbVar K}

/-- The trivial point through `ε`. -/
theorem one_left_ptR (𝒢 : GroupModel A K) (Λ : Type) [CommRing Λ] [Algebra K Λ] :
    (1 : (Over.map (jK K)).obj (ptR (K := K) Λ) ⟶ 𝒢.G).left =
      ptAt 𝒢 (εMap 𝒢 ≫ CommRingCat.ofHom (algebraMap K Λ)) := by
  rw [one_left_N, ← ptAt_specMap, ptAt_εMap]
  rfl

omit [NumberField K] in
theorem isLocalHom_algebraMap_tsze :
    IsLocalHom (algebraMap K (TrivSqZeroExt K K)) := by
  refine ⟨fun a ha => ?_⟩
  rw [isUnit_iff_isUnit_fst] at ha
  simpa [algebraMap_eq_inl] using ha

/-- **A derivation at the origin killing `𝓞_K` and `f^*` vanishes.** -/
theorem derivation_eq_zero (hM : AvSplit.MilneIsogenyQuasiInverse) (φ : A.X ⟶ B.X)
    (hφ : IsIsogeny φ) (𝒩A : GroupModel A K) (𝒩B : GroupModel B K) (f : 𝒩A.G ⟶ 𝒩B.G)
    [IsMonHom f] (he : CToPrinted.ExtendsIsogeny φ 𝒩A 𝒩B f) (D : 𝒩A.genStalk → K)
    (hadd : ∀ a b, D (a + b) = D a + D b)
    (hmul : ∀ a b, D (a * b) = (εMap 𝒩A).hom a * D b + (εMap 𝒩A).hom b * D a)
    (hs : ∀ c, D (𝒩A.structMap c) = 0) (hg : ∀ b, D ((genMap 𝒩A 𝒩B f).hom b) = 0) :
    ∀ r, D r = 0 := by
  set ev := (εMap 𝒩A).hom
  let ρ : 𝒩A.genStalk ⟶ CommRingCat.of (TrivSqZeroExt K K) :=
    CommRingCat.ofHom (dualHom ev D hadd hmul)
  have hρ_apply : ∀ r, ρ.hom r = inl (ev r) + inr (D r) := fun r => rfl
  haveI : IsLocalHom ρ.hom := by
    refine ⟨fun r hr => ?_⟩
    rw [isUnit_iff_isUnit_fst, hρ_apply] at hr
    simp only [fst_add, fst_inl, fst_inr, add_zero] at hr
    exact isUnit_of_map_unit ev r hr
  let α : CommRingCat.of K ⟶ CommRingCat.of (TrivSqZeroExt K K) :=
    CommRingCat.ofHom (algebraMap K (TrivSqZeroExt K K))
  haveI : IsLocalHom (εMap 𝒩A ≫ α).hom := by
    haveI := isLocalHom_algebraMap_tsze (K := K)
    rw [CommRingCat.hom_comp]
    exact RingHom.isLocalHom_comp _ _
  have hρs : sm 𝒩A ≫ ρ = CommRingCat.ofHom (algebraMap (𝓞 K) K) ≫ α := by
    refine CommRingCat.hom_ext (RingHom.ext fun c => ?_)
    show ρ.hom (𝒩A.structMap c) = algebraMap K (TrivSqZeroExt K K) (algebraMap (𝓞 K) K c)
    rw [hρ_apply, hs, εMap_structMap, algebraMap_eq_inl, inr_zero, add_zero]
  let T := ptR (K := K) (TrivSqZeroExt K K)
  let vN : (Over.map (jK K)).obj T ⟶ 𝒩A.G := Over.homMk (ptAt 𝒩A ρ) (by
    show ptAt 𝒩A ρ ≫ 𝒩A.G.hom = Spec.map α ≫ jK K
    rw [ptAt_hom, hρs, Spec.map_comp])
  let v := theta 𝒩A T vN
  -- `v` is a tangent vector at the origin
  have hv1 : AtOrigin A v := by
    show specHom (fstHom K K K) ≫ theta 𝒩A T vN = 1
    rw [← theta_nat]
    have h1 : (Over.map (jK K)).map (specHom (fstHom K K K)) ≫ vN = 1 := by
      apply Over.OverMorphism.ext
      rw [Over.comp_left, one_left_ptR]
      show Spec.map (CommRingCat.ofHom ((fstHom K K K : TrivSqZeroExt K K →ₐ[K] K) :
        TrivSqZeroExt K K →+* K)) ≫ ptAt 𝒩A ρ = _
      rw [ptAt_specMap]
      congr 1
      refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
      show (ρ.hom r).fst = algebraMap K K (ev r)
      rw [hρ_apply]
      simp
    rw [h1, theta_one]
  -- `v ≫ φ = 1`
  have hv2 : v ≫ φ = 1 := by
    rw [← theta_comp 𝒩A 𝒩B φ f he]
    have h1 : vN ≫ f = 1 := by
      apply Over.OverMorphism.ext
      rw [Over.comp_left, one_left_ptR]
      show ptAt 𝒩A ρ ≫ f.left = _
      rw [ptAt_comp]
      congr 1
      refine CommRingCat.hom_ext (RingHom.ext fun b => ?_)
      show ρ.hom ((genMap 𝒩A 𝒩B f).hom b) =
        algebraMap K (TrivSqZeroExt K K) ((εMap 𝒩B).hom b)
      rw [hρ_apply, hg, ← genMap_εMap 𝒩A 𝒩B f, algebraMap_eq_inl, inr_zero, add_zero]
      rfl
    rw [h1, theta_one]
  -- Milne's quasi-inverse
  haveI := hφ.1
  obtain ⟨d, hd, ψ, h1, -⟩ := hM K A B (PkgI3.AbVar.Hom.mk' φ) ⟨hφ.2.1, hφ.2.2⟩
  have hv3 : v ≫ (((d : ℤ) : PkgI3.AbVar.End A)).hom = 1 := by
    rw [← h1, PkgI3.AbVar.Hom.hom_mk', ← Category.assoc, hv2, MonObj.one_comp]
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := A.X.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (orig A (IsLocalRing.closedPoint K))) isOpen_univ
  have hv : v = 1 := eq_one_of_comp_intCast A hxU hU hv1 d (by exact_mod_cast hd.ne') hv3
  have hvN : vN = 1 := (theta 𝒩A T).injective (hv.trans (theta_one 𝒩A T).symm)
  have hρε : ρ = εMap 𝒩A ≫ α := by
    apply ptAt_injective 𝒩A
    have := congrArg Over.Hom.left hvN
    rw [one_left_ptR] at this
    exact this
  intro r
  have := congrArg (fun g => (g.hom r).snd) hρε
  simp only [hρ_apply, CommRingCat.hom_comp, RingHom.comp_apply, α, CommRingCat.hom_ofHom,
    algebraMap_eq_inl, snd_add, snd_inl, snd_inr, zero_add] at this
  exact this

end Tan

end GapHeight

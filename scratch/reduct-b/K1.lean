import RBBase

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)

namespace ReductB
open ReductSplit ReductGlue ZInQ.Contrib.AbVarBC

section Descent

variable {K : Type} [Field K]

/-- A separable element of `K̄` over an intermediate field `F`, fixed by `Aut(K̄/F)`, lies in `F`. -/
theorem mem_of_isSeparable_of_fixed_inter (F : IntermediateField K (AlgebraicClosure K))
    (a : AlgebraicClosure K) (ha : IsSeparable F a)
    (hfix : ∀ σ : AlgebraicClosure K ≃ₐ[F] AlgebraicClosure K, σ a = a) :
    a ∈ Set.range (algebraMap F (AlgebraicClosure K)) := by
  have : IsAlgClosure F (AlgebraicClosure K) :=
    ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := K) F⟩
  let L := separableClosure F (AlgebraicClosure K)
  have haL : a ∈ L := (mem_separableClosure_iff).mpr ha
  let a' : L := ⟨a, haL⟩
  have : a' ∈ Set.range (algebraMap F L) := by
    rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
    intro τ
    apply Subtype.ext
    have h1 := AlgEquiv.liftNormal_commutes τ (AlgebraicClosure K) a'
    have h2 : (algebraMap L (AlgebraicClosure K)) a' = a := rfl
    rw [h2, hfix] at h1
    exact h1.symm
  obtain ⟨c, hc⟩ := this
  exact ⟨c, by rw [IsScalarTower.algebraMap_apply F L (AlgebraicClosure K), hc]; rfl⟩

/-- **Galois descent to an intermediate field for points of an étale `K`-scheme**: a `K̄`-point
fixed by every `σ ∈ Aut(K̄/K)` that fixes `F` pointwise comes from an `F`-point. -/
theorem exists_rational_of_fixed_etale_inter (F : IntermediateField K (AlgebraicClosure K))
    (X : Over (Spec (CommRingCat.of K)))
    [Etale X.hom] (q : PkgI3.AbVar.ptObj (K := K) (AlgebraicClosure K) ⟶ X)
    (hq : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, (∀ y ∈ F, σ y = y) →
      PkgI3.AbVar.galHom σ ≫ q = q) :
    ∃ y : PkgI3.AbVar.ptObj (K := K) F ⟶ X, extHom F.val ≫ y = q := by
  classical
  let q0 : Spec (CommRingCat.of (AlgebraicClosure K)) ⟶ X.left := q.left
  have hq0 : q0 ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) :=
    Over.w q
  let p : X.left := q0 (IsLocalRing.closedPoint (AlgebraicClosure K))
  obtain ⟨_, ⟨U, hU, rfl⟩, hpU, -⟩ :=
    X.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ p) isOpen_univ
  change X.left.Opens at U
  change IsAffineOpen U at hU
  have hrange : Set.range q0 ⊆ Set.range U.ι := by
    rintro _ ⟨s, rfl⟩
    rw [Scheme.Opens.range_ι]
    have : s = IsLocalRing.closedPoint (AlgebraicClosure K) :=
      Subsingleton.elim (α := PrimeSpectrum (AlgebraicClosure K)) _ _
    rw [this]
    exact hpU
  let q' := IsOpenImmersion.lift U.ι q0 hrange
  have hq' : q' ≫ U.ι = q0 := IsOpenImmersion.lift_fac _ _ _
  let e := hU.isoSpec
  let φ : Γ(X.left, U) ⟶ CommRingCat.of (AlgebraicClosure K) := Spec.preimage (q' ≫ e.hom)
  let θ : CommRingCat.of K ⟶ Γ(X.left, U) := Spec.preimage (e.inv ≫ U.ι ≫ X.hom)
  have hφ : Spec.map φ = q' ≫ e.hom := Spec.map_preimage _
  have hθ : Spec.map θ = e.inv ≫ U.ι ≫ X.hom := Spec.map_preimage _
  have hql : q0 = Spec.map φ ≫ e.inv ≫ U.ι := by
    rw [hφ, Category.assoc, e.hom_inv_id_assoc, hq']
  have hcomp : θ ≫ φ = CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, hθ, Category.assoc, e.hom_inv_id_assoc, ← Category.assoc q', hq', hq0]
  have hfixφ : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, (∀ y ∈ F, σ y = y) →
      φ ≫ CommRingCat.ofHom (σ : AlgebraicClosure K →+* AlgebraicClosure K) = φ := by
    intro σ hσ
    have h1 := congrArg Over.Hom.left (hq σ hσ)
    change Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure K →+* AlgebraicClosure K)) ≫ q0 =
      q0 at h1
    rw [hql, ← Category.assoc, ← Spec.map_comp] at h1
    have h2 := (cancel_mono (e.inv ≫ U.ι)).mp h1
    exact Spec.map_injective h2
  have hθet : RingHom.Etale θ.hom := by
    have : Etale (Spec.map θ) := by rw [hθ]; infer_instance
    exact HasRingHomProperty.Spec_iff.mp this
  letI : Algebra K Γ(X.left, U) := θ.hom.toAlgebra
  have : Algebra.Etale K Γ(X.left, U) := hθet
  let f : Γ(X.left, U) →ₐ[K] AlgebraicClosure K :=
    { φ.hom with
      commutes' := fun a => congrArg (fun g => CommRingCat.Hom.hom g a) hcomp }
  have hmem : ∀ r, φ.hom r ∈ Set.range (algebraMap F (AlgebraicClosure K)) := by
    intro r
    refine mem_of_isSeparable_of_fixed_inter F _ ((isSeparable_of_etale f r).tower_top F)
      fun τ => ?_
    exact congrArg (fun f => CommRingCat.Hom.hom f r)
      (hfixφ (τ.restrictScalars K) (fun y hy => τ.commutes ⟨y, hy⟩))
  choose c hc using hmem
  have hinj := (algebraMap F (AlgebraicClosure K)).injective
  let ψ : Γ(X.left, U) →+* F :=
    { toFun := c
      map_one' := hinj (by rw [hc, map_one, map_one])
      map_mul' := fun a b => hinj (by rw [hc, map_mul, map_mul, hc, hc])
      map_zero' := hinj (by rw [hc, map_zero, map_zero])
      map_add' := fun a b => hinj (by rw [hc, map_add, map_add, hc, hc]) }
  have hθψ : θ ≫ CommRingCat.ofHom ψ = CommRingCat.ofHom (algebraMap K F) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    apply hinj
    have := congrArg (fun f => CommRingCat.Hom.hom f a) hcomp
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this ⊢
    rw [show algebraMap F (AlgebraicClosure K) (ψ (θ.hom a)) = φ.hom (θ.hom a) from hc _, this]
    rfl
  refine ⟨Over.homMk (Spec.map (CommRingCat.ofHom ψ) ≫ e.inv ≫ U.ι) ?_, ?_⟩
  · show (Spec.map (CommRingCat.ofHom ψ) ≫ e.inv ≫ U.ι) ≫ X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap K F))
    rw [Category.assoc, Category.assoc, ← hθ, ← Spec.map_comp, hθψ]
  · apply Over.OverMorphism.ext
    show Spec.map (CommRingCat.ofHom ((F.val : F →ₐ[K] AlgebraicClosure K) :
        F →+* AlgebraicClosure K)) ≫ Spec.map (CommRingCat.ofHom ψ) ≫ e.inv ≫ U.ι = q0
    rw [hql, ← Category.assoc, ← Spec.map_comp]
    congr 2
    ext r
    exact hc r

/-- **Torsion points fixed by `Aut(K̄/F)` are `F`-rational** (from the bundle leaf
`MulEtaleAbelianScheme`): the intermediate-field form of `fixedTorsionRational_of_mulEtale`. -/
theorem fixedTorsionRational_inter (hE : AvSplit.T4.MulEtaleAbelianScheme)
    (F : IntermediateField K (AlgebraicClosure K)) (A : PkgI3.AbVar K) (m : ℕ) (hm : (m : K) ≠ 0)
    (x : A.Pt (AlgebraicClosure K)) (hx : x ^ m = 1)
    (hfix : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, (∀ y ∈ F, σ y = y) →
      A.galAct σ x = x) :
    ∃ z : A.Pt F, extPt A F.val z = x := by
  haveI : PkgI2.IsAbelianScheme (Grp.mk A.X) := ⟨inferInstanceAs (IsProper A.X.hom),
    inferInstanceAs (Smooth A.X.hom), inferInstanceAs (GeometricallyConnected A.X.hom)⟩
  have het : Etale ((𝟙 A.X ^ m : A.X ⟶ A.X).left) :=
    hE K (Grp.mk A.X) m (isUnit_iff_ne_zero.mpr hm)
  let M : A.X ⟶ A.X := 𝟙 A.X ^ m
  let P : Over (Spec (CommRingCat.of K)) := Over.mk (pullback.snd M.left (η[A.X]).left)
  haveI : Etale P.hom := by
    change Etale (pullback.snd M.left (η[A.X]).left)
    infer_instance
  have hxm : x ≫ M = 1 := by rw [comp_pow_one]; exact hx
  have hw : x.left ≫ M.left =
      (PkgI3.AbVar.ptObj (K := K) (AlgebraicClosure K)).hom ≫ (η[A.X]).left := by
    have h1 := congrArg Over.Hom.left hxm
    rw [Over.comp_left] at h1
    rw [h1]
    change (toUnit _ ≫ η[A.X]).left = _
    rw [Over.comp_left]
    congr 1
  let x' : PkgI3.AbVar.ptObj (K := K) (AlgebraicClosure K) ⟶ P :=
    Over.homMk (pullback.lift x.left _ hw) (by simp [P])
  have hfix' : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, (∀ y ∈ F, σ y = y) →
      PkgI3.AbVar.galHom σ ≫ x' = x' := by
    intro σ hσ
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp only [x', Over.comp_left, Over.homMk_left, Category.assoc, pullback.lift_fst]
      exact congrArg Over.Hom.left (hfix σ hσ)
    · simp only [x', Over.comp_left, Over.homMk_left, Category.assoc, pullback.lift_snd]
      exact Over.w (PkgI3.AbVar.galHom σ)
  obtain ⟨y', hy'⟩ := exists_rational_of_fixed_etale_inter F P x' hfix'
  have hpr : pullback.fst M.left (η[A.X]).left ≫ A.X.hom = P.hom := by
    change _ = pullback.snd M.left (η[A.X]).left
    rw [← Over.w M, ← Category.assoc, pullback.condition, Category.assoc, Over.w η[A.X]]
    simp
  let pr : P ⟶ A.X := Over.homMk (pullback.fst M.left (η[A.X]).left) hpr
  refine ⟨y' ≫ pr, ?_⟩
  change extHom _ ≫ y' ≫ pr = x
  rw [← Category.assoc, hy']
  apply Over.OverMorphism.ext
  simp [x', pr]

end Descent

/-- `3` or `4` is a unit in a local ring (`4 - 3 = 1`). -/
theorem exists_three_le_isUnit {R : Type} [CommRing R] [IsLocalRing R] :
    ∃ m : ℕ, 3 ≤ m ∧ IsUnit (m : R) := by
  by_cases h3 : IsUnit ((3 : ℕ) : R)
  · exact ⟨3, le_rfl, h3⟩
  · refine ⟨4, by norm_num, ?_⟩
    have h1 : IsUnit (((4 : ℕ) : R) + -((3 : ℕ) : R)) := by
      rw [show ((4 : ℕ) : R) + -((3 : ℕ) : R) = 1 by push_cast; ring]
      exact isUnit_one
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h1 with h | h
    · exact h
    · exact absurd (IsUnit.neg_iff _ |>.mp h) h3

/-- **K1: SGA 7 IX 3.6 over a DVR from Raynaud's criterion (4.7)**, with the bundle leaves
`MumfordTorsionAlgClosed` (finiteness of `A(K̄)[m]`) and `MulEtaleAbelianScheme` (`[m]` étale).
Take `m ∈ {3, 4}` invertible in `O`, `K'` a finite field of definition of `A(K̄)[m]`
(`torsionFieldOfDefinition_of`); at every DVR `O'` of `K'` over `O` the points of order `m` of
`A_{K'}` are `K'`-rational (`torsion_descends_etale` and `fixedTorsionRational_inter`), so Raynaud's
criterion applies to `A_{K'}` over `O'`. -/
theorem semistableReductionDVR_of_raynaud (hR : RaynaudSemistable)
    (hM : AvSplit.MumfordTorsionAlgClosed) (hE : AvSplit.T4.MulEtaleAbelianScheme) :
    SemistableReductionDVR := by
  intro K _ O _ A
  obtain ⟨m, hm3, hmu⟩ := exists_three_le_isUnit (R := O)
  have hmK : (m : K) ≠ 0 := natCast_ne_zero_of_isUnit O hmu
  obtain ⟨K', hfin, hfix⟩ :=
    torsionFieldOfDefinition_of (AvSplit.torsionStructure_of_mumford hM) K A m hmK
  refine ⟨K', hfin, fun O' hO'dvr hO => ?_⟩
  haveI := hO'dvr
  have hmu' : IsUnit (m : O') := by
    have := hmu.map (comapHom hO)
    rwa [map_natCast] at this
  refine hR K' O' (A.baseChange K') m hm3 hmu' ?_
  intro x hx
  haveI : Algebra.IsAlgebraic K' (AlgebraicClosure K) := Algebra.IsAlgebraic.tower_top (K := K) K'
  haveI : Module.IsTorsionFree K' (AlgebraicClosure K') :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (algebraMap K' (AlgebraicClosure K')).injective
  haveI : Module.IsTorsionFree K' (AlgebraicClosure K) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (algebraMap K' (AlgebraicClosure K)).injective
  let κ' : AlgebraicClosure K →ₐ[K'] AlgebraicClosure K' := IsAlgClosed.lift
  let κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure K' := κ'.restrictScalars K
  obtain ⟨p, hp, hpx⟩ := torsion_descends_etale hE A κ m hmK x hx
  obtain ⟨z, hz⟩ := fixedTorsionRational_inter hE K' A m hmK p hp (fun σ hσ => hfix σ hσ p hp)
  refine ⟨(bcPt A K').symm z, ?_⟩
  rw [← hpx, ← hz]
  apply (bcPt A (AlgebraicClosure K')).injective
  rw [MulEquiv.apply_symm_apply, bcPt_extPt, MulEquiv.apply_symm_apply, extPt_extPt]
  have hκ : AlgHom.restrictScalars K (Algebra.ofId K' (AlgebraicClosure K')) = κ.comp K'.val := by
    refine AlgHom.ext fun a => ?_
    exact (κ'.commutes a).symm
  rw [hκ]

end ReductB

#print axioms ReductB.semistableReductionDVR_of_raynaud

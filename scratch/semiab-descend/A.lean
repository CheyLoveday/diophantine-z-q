import ZInQKernel.Contrib.OneProof.PrintedStableHeight
import ZInQKernel.Contrib.OneProof.GeomConnOfRationalPoint

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open DictModels.RaynaudOr ZInQ.HeightSplit

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace ZInQ.SemiAbDescend

/-! ## §1. Points over affine schemes determine morphisms -/

section Yoneda

variable {S : Scheme.{0}}

/-- The affine open cover of `T.left`. -/
abbrev cov (T : Over S) : T.left.OpenCover := T.left.affineOpenCover.openCover

/-- The pieces of the affine open cover of `T.left`, as objects over `S`. -/
abbrev coverObj (T : Over S) (x : (cov T).I₀) : Over S :=
  Over.mk ((cov T).f x ≫ T.hom)

/-- The inclusion of a cover piece. -/
abbrev coverMap (T : Over S) (x : (cov T).I₀) : coverObj T x ⟶ T :=
  Over.homMk ((cov T).f x) rfl

theorem isAffine_coverObj (T : Over S) (x : (cov T).I₀) : IsAffine (coverObj T x).left := by
  change IsAffine (Spec _); infer_instance

/-- Injectivity on all test objects from injectivity on affine ones. -/
theorem injective_of_affine {X Y : Over S} (f : X ⟶ Y)
    (h : ∀ T : Over S, IsAffine T.left → Function.Injective (fun a : T ⟶ X => a ≫ f))
    (T : Over S) : Function.Injective (fun a : T ⟶ X => a ≫ f) := by
  intro a b hab
  simp only at hab
  apply Over.OverMorphism.ext
  refine Scheme.Cover.hom_ext (cov T) _ _ fun x => ?_
  have := h (coverObj T x) (isAffine_coverObj T x) (a₁ := coverMap T x ≫ a) (a₂ := coverMap T x ≫ b)
    (by simp only [Category.assoc, hab])
  exact congrArg CommaMorphism.left this

/-- **Yoneda on affine test objects**: a morphism over `S` that is bijective on points with values in
affine schemes is an isomorphism. -/
theorem isIso_of_bijective_affine {X Y : Over S} (f : X ⟶ Y)
    (h : ∀ T : Over S, IsAffine T.left → Function.Bijective (fun a : T ⟶ X => a ≫ f)) :
    IsIso f := by
  have hinj := injective_of_affine f (fun T hT => (h T hT).1)
  choose a ha using fun x => (h (coverObj Y x) (isAffine_coverObj Y x)).2 (coverMap Y x)
  have ha' : ∀ x, a x ≫ f = coverMap Y x := ha
  have hcompat : ∀ x y : (cov Y).I₀, pullback.fst ((cov Y).f x) ((cov Y).f y) ≫ (a x).left =
      pullback.snd ((cov Y).f x) ((cov Y).f y) ≫ (a y).left := by
    intro x y
    let P : Over S := Over.mk (pullback.fst ((cov Y).f x) ((cov Y).f y) ≫ (cov Y).f x ≫ Y.hom)
    let p1 : P ⟶ coverObj Y x := Over.homMk (pullback.fst ((cov Y).f x) ((cov Y).f y)) rfl
    let p2 : P ⟶ coverObj Y y := Over.homMk (pullback.snd ((cov Y).f x) ((cov Y).f y)) (by
      simp only [P, coverObj, Over.mk_hom]
      rw [pullback.condition_assoc])
    have := hinj P (a₁ := p1 ≫ a x) (a₂ := p2 ≫ a y) (by
      simp only [Category.assoc, ha']
      apply Over.OverMorphism.ext
      simp only [Over.comp_left, Over.homMk_left, p1, p2]
      exact pullback.condition)
    exact congrArg CommaMorphism.left this
  let gl : Y.left ⟶ X.left := (cov Y).glueMorphisms (fun x => (a x).left) hcompat
  have hgl : ∀ x, (cov Y).f x ≫ gl = (a x).left := fun x => (cov Y).ι_glueMorphisms _ hcompat x
  have hw : gl ≫ X.hom = Y.hom := by
    refine Scheme.Cover.hom_ext (cov Y) _ _ fun x => ?_
    rw [← Category.assoc, hgl, Over.w]
    rfl
  let g : Y ⟶ X := Over.homMk gl hw
  have hgf : g ≫ f = 𝟙 Y := by
    apply Over.OverMorphism.ext
    refine Scheme.Cover.hom_ext (cov Y) _ _ fun x => ?_
    simp only [Over.comp_left, Over.homMk_left, Over.id_left, Category.comp_id, g]
    rw [← Category.assoc, hgl, ← Over.comp_left, ha']
    rfl
  have hfg : f ≫ g = 𝟙 X := hinj X (a₁ := f ≫ g) (a₂ := 𝟙 X) (by
    simp only [Category.assoc, hgf, Category.comp_id, Category.id_comp])
  exact ⟨g, hfg, hgf⟩

end Yoneda

/-! ## §2. Affine schemes over `K` are `Spec` of `K`-algebras -/

section AlgPt

variable {K : Type} [Field K]

/-- Every morphism between `Spec`s of `K`-algebras over `K` is `Spec` of a `K`-algebra map. -/
theorem exists_algPtMap {R S : Type} [CommRing R] [Algebra K R] [CommRing S] [Algebra K S]
    (f : algPt K R ⟶ algPt K S) : ∃ ψ : S →ₐ[K] R, f = algPtMap ψ := by
  obtain ⟨ψ0, hψ0⟩ : ∃ ψ0 : CommRingCat.of S ⟶ CommRingCat.of R, Spec.map ψ0 = f.left :=
    ⟨Spec.preimage f.left, Spec.map_preimage _⟩
  have hw : f.left ≫ Spec.map (CommRingCat.ofHom (algebraMap K S)) =
      Spec.map (CommRingCat.ofHom (algebraMap K R)) := Over.w f
  have hc : CommRingCat.ofHom (algebraMap K S) ≫ ψ0 = CommRingCat.ofHom (algebraMap K R) :=
    Spec.map_injective (by rw [Spec.map_comp, hψ0]; exact hw)
  refine ⟨{ ψ0.hom with commutes' := fun c => ?_ }, ?_⟩
  · have := congrArg (fun g => g.hom c) hc
    simpa using this
  · apply Over.OverMorphism.ext
    simp only [algPtMap, Over.homMk_left]
    rw [← hψ0]
    rfl

/-- An affine scheme over `K` is isomorphic over `K` to `Spec` of a `K`-algebra. -/
theorem exists_iso_algPt (T : Over (Spec (CommRingCat.of K))) [IsAffine T.left] :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra K R), Nonempty (T ≅ algPt K R) := by
  let ψ : CommRingCat.of K ⟶ Γ(T.left, ⊤) := Spec.preimage (T.left.isoSpec.inv ≫ T.hom)
  letI : Algebra K Γ(T.left, ⊤) := ψ.hom.toAlgebra
  refine ⟨Γ(T.left, ⊤), inferInstance, this, ⟨Over.isoMk T.left.isoSpec ?_⟩⟩
  have h1 : Spec.map ψ = T.left.isoSpec.inv ≫ T.hom := Spec.map_preimage _
  show T.left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ψ.hom) = T.hom
  change T.left.isoSpec.hom ≫ Spec.map ψ = T.hom
  rw [h1, Iso.hom_inv_id_assoc]

/-- Bijectivity on all affine points from bijectivity on `Spec` of `K`-algebras. -/
theorem bijective_affine_of_algPt {X Y : Over (Spec (CommRingCat.of K))} (f : X ⟶ Y)
    (h : ∀ (R : Type) [CommRing R] [Algebra K R],
      Function.Bijective (fun a : algPt K R ⟶ X => a ≫ f))
    (T : Over (Spec (CommRingCat.of K))) (hT : IsAffine T.left) :
    Function.Bijective (fun a : T ⟶ X => a ≫ f) := by
  obtain ⟨R, _, _, ⟨i⟩⟩ := exists_iso_algPt T
  have e1 : (T ⟶ X) ≃ (algPt K R ⟶ X) := (i.homCongr (Iso.refl X))
  have e2 : (T ⟶ Y) ≃ (algPt K R ⟶ Y) := (i.homCongr (Iso.refl Y))
  have hcomm : (fun a : T ⟶ X => a ≫ f) =
      (i.homCongr (Iso.refl Y)).symm ∘ (fun a : algPt K R ⟶ X => a ≫ f) ∘ (i.homCongr (Iso.refl X)) := by
    funext a
    simp [Iso.homCongr]
  rw [hcomm]
  exact (Equiv.bijective _).comp ((h R).comp (Equiv.bijective _))

end AlgPt


/-! ## §3. A kernel that is a split torus in the functor of points is `Spec K[x^{±1}]` -/

section Torus

variable {K : Type} [Field K]

/-- The coordinate ring `K[x₁^{±1}, …, x_r^{±1}]` of the split torus `𝔾_m^r`. -/
abbrev TorusRing (K : Type) [Field K] (r : ℕ) : Type :=
  Localization.Away (∏ i : Fin r, MvPolynomial.X i : MvPolynomial (Fin r) K)

theorem isUnit_X {r : ℕ} (i : Fin r) :
    IsUnit (algebraMap (MvPolynomial (Fin r) K) (TorusRing K r) (MvPolynomial.X i)) := by
  have hu := IsLocalization.Away.algebraMap_isUnit (S := TorusRing K r)
    (∏ i : Fin r, MvPolynomial.X i : MvPolynomial (Fin r) K)
  exact isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))) hu

/-- The universal point `(x₁, …, x_r)` of `𝔾_m^r`. -/
def tUniv (r : ℕ) : Fin r → (TorusRing K r)ˣ := fun i => (isUnit_X i).unit

/-- The `K`-algebra map `K[x^{±1}] → R`, `xᵢ ↦ tᵢ`. -/
def torusLift {r : ℕ} {R : Type} [CommRing R] [Algebra K R] (t : Fin r → Rˣ) :
    TorusRing K r →ₐ[K] R :=
  IsLocalization.liftAlgHom (M := Submonoid.powers (∏ i : Fin r, MvPolynomial.X i :
      MvPolynomial (Fin r) K)) (f := MvPolynomial.aeval (fun i => (t i : R))) (by
    rintro ⟨y, n, rfl⟩
    simp only [map_pow, map_prod, MvPolynomial.aeval_X]
    have : (∏ i, (t i : R)) = ((∏ i, t i : Rˣ) : R) := by simp [Units.coe_prod]
    rw [this]
    exact IsUnit.pow n (Units.isUnit _))

theorem torusLift_tUniv {r : ℕ} {R : Type} [CommRing R] [Algebra K R] (t : Fin r → Rˣ) (i : Fin r) :
    torusLift t ((tUniv r i : (TorusRing K r)ˣ) : TorusRing K r) = t i := by
  simp only [tUniv, IsUnit.unit_spec, torusLift, IsLocalization.liftAlgHom_apply,
    IsLocalization.lift_eq]
  simp

theorem algHom_ext_torus {r : ℕ} {R : Type} [CommRing R] [Algebra K R]
    (ψ₁ ψ₂ : TorusRing K r →ₐ[K] R)
    (h : ∀ i, ψ₁ ((tUniv r i : (TorusRing K r)ˣ) : TorusRing K r) =
      ψ₂ ((tUniv r i : (TorusRing K r)ˣ) : TorusRing K r)) : ψ₁ = ψ₂ := by
  apply IsLocalization.algHom_ext (Submonoid.powers (∏ i : Fin r, MvPolynomial.X i :
    MvPolynomial (Fin r) K))
  apply MvPolynomial.algHom_ext
  intro i
  show ψ₁ (algebraMap _ _ (MvPolynomial.X i)) = ψ₂ (algebraMap _ _ (MvPolynomial.X i))
  simpa [tUniv] using h i

end Torus

/-! ## §4. Kernels -/

section Ker

variable {K : Type} [Field K]

/-- The scheme-theoretic kernel of `π : G → B` (fibre product with the unit section of `B`). -/
abbrev kerObj {G B : Over (Spec (CommRingCat.of K))} [GrpObj B] (π : G ⟶ B) :
    Over (Spec (CommRingCat.of K)) :=
  pullback π η[B]

/-- The kernel is a smooth connected affine `K`-scheme. -/
def IsSmoothConnAffineKer {G B : Over (Spec (CommRingCat.of K))} [GrpObj B] (π : G ⟶ B) : Prop :=
  Smooth (kerObj π).hom ∧ IsAffine (kerObj π).left ∧ ConnectedSpace (kerObj π).left

instance (r : ℕ) : IsDomain (TorusRing K r) :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors
    (Finset.prod_ne_zero_iff.mpr fun i _ => MvPolynomial.X_ne_zero i))

theorem smooth_algPt_torus (r : ℕ) : Smooth (algPt K (TorusRing K r)).hom := by
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap K (TorusRing K r))))
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  change RingHom.Smooth (algebraMap K (TorusRing K r))
  rw [RingHom.smooth_algebraMap]
  haveI : Algebra.Smooth K (MvPolynomial (Fin r) K) := inferInstance
  haveI : Algebra.Smooth (MvPolynomial (Fin r) K) (TorusRing K r) := inferInstance
  exact Algebra.Smooth.comp K (MvPolynomial (Fin r) K) (TorusRing K r)

/-- **A kernel that is a split torus in the functor of points is smooth, connected and affine**: it is
`Spec K[x₁^{±1}, …, x_r^{±1}]` (Yoneda on affine test schemes). -/
theorem isSmoothConnAffineKer_of_torus {U B : Over (Spec (CommRingCat.of K))} [GrpObj U] [GrpObj B]
    (π : U ⟶ B) (r : ℕ) (e : ∀ (R : Type) [CommRing R] [Algebra K R], (Fin r → Rˣ) →* (algPt K R ⟶ U))
    (he_inj : ∀ (R : Type) [CommRing R] [Algebra K R], Function.Injective (e R))
    (he_ker : ∀ (R : Type) [CommRing R] [Algebra K R] (u : algPt K R ⟶ U), u ≫ π = 1 ↔ u ∈ (e R).range)
    (he_nat : ∀ (R S : Type) [CommRing R] [Algebra K R] [CommRing S] [Algebra K S] (f : R →ₐ[K] S)
      (t : Fin r → Rˣ), e S (fun i => Units.map (f : R →* S) (t i)) = algPtMap f ≫ e R t) :
    IsSmoothConnAffineKer π := by
  let L := TorusRing K r
  have hk : e L (tUniv r) ≫ π = toUnit _ ≫ η[B] := by
    rw [(he_ker L _).mpr ⟨tUniv r, rfl⟩]; rfl
  let j : algPt K L ⟶ kerObj π := pullback.lift (e L (tUniv r)) (toUnit _) hk
  have hj1 : j ≫ pullback.fst π η[B] = e L (tUniv r) := pullback.lift_fst _ _ _
  have hmap : ∀ (R : Type) [CommRing R] [Algebra K R] (ψ : L →ₐ[K] R),
      algPtMap ψ ≫ e L (tUniv r) = e R (fun i => Units.map (ψ : L →* R) (tUniv r i)) :=
    fun R _ _ ψ => (he_nat L R ψ (tUniv r)).symm
  have hbij : ∀ (R : Type) [CommRing R] [Algebra K R],
      Function.Bijective (fun a : algPt K R ⟶ algPt K L => a ≫ j) := by
    intro R _ _
    constructor
    · intro a₁ a₂ h
      simp only at h
      obtain ⟨ψ₁, rfl⟩ := exists_algPtMap a₁
      obtain ⟨ψ₂, rfl⟩ := exists_algPtMap a₂
      have h2 := congrArg (· ≫ pullback.fst π η[B]) h
      simp only [Category.assoc, hj1, hmap] at h2
      have h3 := he_inj R h2
      rw [algHom_ext_torus ψ₁ ψ₂ fun i => by
        have := congrArg (fun t => ((t i : Rˣ) : R)) h3
        simpa using this]
    · intro b
      have hb : (b ≫ pullback.fst π η[B]) ≫ π = 1 := by
        rw [Category.assoc, pullback.condition, ← Category.assoc]
        rw [toUnit_unique (b ≫ pullback.snd π η[B]) (toUnit _)]
        rfl
      obtain ⟨t, ht⟩ := (he_ker R _).mp hb
      refine ⟨algPtMap (torusLift t), ?_⟩
      apply pullback.hom_ext
      · simp only [Category.assoc, hj1, hmap]
        rw [← ht]
        congr 1
        funext i
        ext
        exact torusLift_tUniv t i
      · exact toUnit_unique _ _
  haveI : IsIso j := isIso_of_bijective_affine j (bijective_affine_of_algPt j hbij)
  let E := asIso j
  have hw : (kerObj π).hom = E.inv.left ≫ (algPt K L).hom := (Over.w E.inv).symm
  refine ⟨?_, ?_, ?_⟩
  · rw [hw]
    haveI := smooth_algPt_torus (K := K) r
    infer_instance
  · change IsAffine (kerObj π).left
    haveI : IsAffine (algPt K L).left := by change IsAffine (Spec _); infer_instance
    exact IsAffine.of_isIso E.inv.left
  · haveI : ConnectedSpace (algPt K L).left := by
      change ConnectedSpace (Spec (CommRingCat.of L)); infer_instance
    haveI : IsIso E.hom.left := by change IsIso ((Over.forget _).map E.hom); infer_instance
    exact (E.hom.left.surjective).connectedSpace E.hom.left.continuous

end Ker

end ZInQ.SemiAbDescend

import ZInQKernel.Contrib.OneProof.HeightModelM5.GenericGerm
import ZInQKernel.Contrib.OneProof.HeightModelM5.ExteriorSheaf
import ZInQKernel.Contrib.OneProof.HeightModelM5.ExteriorBaseChange

/-!
# The generic germ of the global sections of `⋀^n e*Ω¹`

Let `f : X ⟶ Spec R₀` be a smooth morphism, `e : Spec R₀ ⟶ X` a morphism and `η` a point of
`Spec R₀` specializing to every point, with injective specialization maps `σ : 𝒪_{S,s} → 𝒪_{S,η}`.
The sheaf `⋀^n e*Ω¹_{X/R₀}` on `S = Spec R₀` is `schemeWedge` of `e*Ω¹`. Its stalk at `s` is
`⋀^n` of the stalk of `e*Ω¹`, which is `𝒪_{S,s} ⊗ Ω[𝒪_{X,e(s)}⁄R₀]` (`pullStalkEquiv`).

* `wedgeGen`: `⋀^n` of the map `stalkToGeneric s` to the generic fibre, semilinear along `σ`.
* `wedgeGen_injective`: it is injective. On an affine chart `U ∋ e(s)` the stalk is
  `𝒪_{S,s} ⊗ Ω[Γ(U)⁄R₀]`, projective since `Γ(U)` is smooth over `R₀`, and the generic fibre is
  its base change to `𝒪_{S,η}` (`exists_baseChange`); so the map is the injective
  `exteriorPowerToBaseChange` followed by `⋀^n` of an isomorphism.
* `rhoTop s`: the map from the stalk of `⋀^n e*Ω¹` at `s` to `⋀^n` of the generic fibre;
  `rhoTop_modSpec`: it commutes with specialization; `rhoTop_injective`.
* `genericGermTop`: global sections of `⋀^n e*Ω¹` to `⋀^n` of the generic fibre;
  `genericGermTop_injective`, `range_genericGermTop` (the intersection of the images of the
  stalks) and `genericGermTop_smul`.

Everything here uses Mathlib and the sheaf constructions of this directory only.
-/

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace KaehlerDifferential
open scoped TensorProduct

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace ZInQ.HeightModelM5

namespace GG

/-! ## `⋀^n` of the map from a stalk to the generic fibre -/

section Wedge

variable {R₀ : Type u} [CommRing R₀] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R₀))
  (e : Spec (CommRingCat.of R₀) ⟶ X) {η : Spec (CommRingCat.of R₀)} (hη : ∀ s, η ⤳ s)
  (s : Spec (CommRingCat.of R₀)) (n : ℕ)

/-- `stalkToGeneric s` as a map semilinear along `σ : 𝒪_{S,s} → 𝒪_{S,η}`. -/
noncomputable def stalkToGenericₛₗ :
    letI := algSt f (e s)
    letI := algBO e s
    letI := algSt f (e η)
    letI := algBO e η
    StalkT f e s →ₛₗ[sig hη s] GenT f e (η := η) :=
  letI := algSt f (e s)
  letI := algBO e s
  letI := algSt f (e η)
  letI := algBO e η
  { toFun := stalkToGeneric f e hη s
    map_add' := map_add _
    map_smul' := stalkToGeneric_smul f e hη s }

theorem stalkToGenericₛₗ_apply (m : StalkT f e s) :
    stalkToGenericₛₗ f e hη s m = stalkToGeneric f e hη s m := rfl

/-- `⋀^n` of the map from the stalk at `s` to the generic fibre. -/
noncomputable def wedgeGen :
    letI := algSt f (e s)
    letI := algBO e s
    letI := algSt f (e η)
    letI := algBO e η
    ⋀[(Spec (CommRingCat.of R₀)).presheaf.stalk s]^n (StalkT f e s) →ₛₗ[sig hη s]
      ⋀[(Spec (CommRingCat.of R₀)).presheaf.stalk η]^n (GenT f e (η := η)) :=
  letI := algSt f (e s)
  letI := algBO e s
  letI := algSt f (e η)
  letI := algBO e η
  wedgeMap (sig hη s) n (stalkToGenericₛₗ f e hη s)

/-- **The generic fibre is the base change of the stalk**, and the stalk is projective: on an
affine chart `U ∋ e(s)`, both are base changes of `Ω[Γ(U)⁄R₀]`, which is projective since
`Γ(U)` is smooth over `R₀`. -/
theorem exists_baseChange [Smooth f] :
    letI := algSt f (e s)
    letI := algBO e s
    letI := algSt f (e η)
    letI := algBO e η
    letI := algOEta hη s
    ∃ G : (Spec (CommRingCat.of R₀)).presheaf.stalk η ⊗[(Spec (CommRingCat.of R₀)).presheaf.stalk s]
        StalkT f e s ≃ₗ[(Spec (CommRingCat.of R₀)).presheaf.stalk η] GenT f e (η := η),
      (∀ m, G (1 ⊗ₜ m) = stalkToGeneric f e hη s m) ∧
        Module.Projective ((Spec (CommRingCat.of R₀)).presheaf.stalk s) (StalkT f e s) := by
  classical
  letI := algSt f (e s)
  letI := algSt f (e η)
  letI := algBO e s
  letI := algBO e η
  letI := algBXi e hη s
  letI := algOEta hη s
  letI := algBEta e hη s
  haveI : IsScalarTower R₀ (X.presheaf.stalk (e s)) (X.presheaf.stalk (e η)) :=
    towerSp f ((hη s).map e.continuous)
  haveI : IsScalarTower (X.presheaf.stalk (e s)) (X.presheaf.stalk (e η))
      ((Spec (CommRingCat.of R₀)).presheaf.stalk η) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (X.presheaf.stalk (e s)) ((Spec (CommRingCat.of R₀)).presheaf.stalk s)
      ((Spec (CommRingCat.of R₀)).presheaf.stalk η) :=
    IsScalarTower.of_algebraMap_eq fun b =>
      congrArg (fun g => g.hom b) (Scheme.Hom.stalkSpecializes_stalkMap e η s (hη s))
  obtain ⟨U, hU, hsU, -⟩ := exists_isAffineOpen_mem_and_subset (x := e s) (U := ⊤) trivial
  have hξU : e η ∈ U := ((hη s).map e.continuous).mem_open U.isOpen hsU
  have hle : U ≤ f ⁻¹ᵁ ⊤ := by simp
  let φ : CommRingCat.of R₀ ⟶ Γ(X, U) :=
    (Scheme.ΓSpecIso (CommRingCat.of R₀)).inv ≫ f.appLE ⊤ U hle
  letI algRA : Algebra R₀ Γ(X, U) := φ.hom.toAlgebra
  haveI hsm : Algebra.Smooth R₀ Γ(X, U) := by
    have h1 := HasRingHomProperty.appLE @Smooth f inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ hle
    have h2 : RingHom.Smooth (Scheme.ΓSpecIso (CommRingCat.of R₀)).inv.hom :=
      RingHom.Smooth.of_bijective (ConcreteCategory.bijective_of_isIso _)
    exact RingHom.Smooth.comp h2 h1
  letI algAB : Algebra Γ(X, U) (X.presheaf.stalk (e s)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨e s, hsU⟩ : U)
  letI algAX : Algebra Γ(X, U) (X.presheaf.stalk (e η)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨e η, hξU⟩ : U)
  haveI hlocB := hU.isLocalization_stalk ⟨e s, hsU⟩
  haveI hlocX := hU.isLocalization_stalk ⟨e η, hξU⟩
  haveI : Algebra.FormallyEtale Γ(X, U) (X.presheaf.stalk (e s)) :=
    Algebra.FormallyEtale.of_isLocalization (hU.primeIdealOf ⟨_, hsU⟩).asIdeal.primeCompl
  haveI : Algebra.FormallyEtale Γ(X, U) (X.presheaf.stalk (e η)) :=
    Algebra.FormallyEtale.of_isLocalization (hU.primeIdealOf ⟨_, hξU⟩).asIdeal.primeCompl
  have hgerm : ∀ (x : X) (hx : x ∈ U) (a : R₀),
      (X.presheaf.germ U x hx).hom (φ.hom a) =
        ((Scheme.ΓSpecIso (CommRingCat.of R₀)).inv ≫ f.appTop ≫
          X.presheaf.germ ⊤ x trivial).hom a := by
    intro x hx a
    simp only [φ, CommRingCat.hom_comp, RingHom.comp_apply, Scheme.Hom.appLE]
    exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
  haveI : IsScalarTower R₀ Γ(X, U) (X.presheaf.stalk (e s)) :=
    IsScalarTower.of_algebraMap_eq fun a => (hgerm _ hsU a).symm
  haveI : IsScalarTower R₀ Γ(X, U) (X.presheaf.stalk (e η)) :=
    IsScalarTower.of_algebraMap_eq fun a => (hgerm _ hξU a).symm
  have hspec : ∀ a : Γ(X, U),
      (X.presheaf.stalkSpecializes ((hη s).map e.continuous)).hom
          ((X.presheaf.germ U _ hsU).hom a) = (X.presheaf.germ U _ hξU).hom a :=
    fun a => TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
  haveI : IsScalarTower Γ(X, U) (X.presheaf.stalk (e s)) (X.presheaf.stalk (e η)) :=
    IsScalarTower.of_algebraMap_eq fun a => (hspec a).symm
  letI algAO : Algebra Γ(X, U) ((Spec (CommRingCat.of R₀)).presheaf.stalk s) :=
    ((e.stalkMap s).hom.comp (algebraMap Γ(X, U) (X.presheaf.stalk (e s)))).toAlgebra
  haveI : IsScalarTower Γ(X, U) (X.presheaf.stalk (e s))
      ((Spec (CommRingCat.of R₀)).presheaf.stalk s) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI algAE : Algebra Γ(X, U) ((Spec (CommRingCat.of R₀)).presheaf.stalk η) :=
    ((e.stalkMap η).hom.comp (algebraMap Γ(X, U) (X.presheaf.stalk (e η)))).toAlgebra
  haveI : IsScalarTower Γ(X, U) (X.presheaf.stalk (e η))
      ((Spec (CommRingCat.of R₀)).presheaf.stalk η) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower Γ(X, U) ((Spec (CommRingCat.of R₀)).presheaf.stalk s)
      ((Spec (CommRingCat.of R₀)).presheaf.stalk η) := IsScalarTower.of_algebraMap_eq fun a => by
    change (e.stalkMap η).hom ((X.presheaf.germ U _ hξU).hom a) =
      sig hη s ((e.stalkMap s).hom ((X.presheaf.germ U _ hsU).hom a))
    rw [← hspec]
    exact congrArg (fun g => g.hom ((X.presheaf.germ U _ hsU).hom a))
      (Scheme.Hom.stalkSpecializes_stalkMap e η s (hη s))
  let E1 := tensorKaehlerEquivOfFormallyEtale R₀ Γ(X, U) (X.presheaf.stalk (e s))
  let E2 := tensorKaehlerEquivOfFormallyEtale R₀ Γ(X, U) (X.presheaf.stalk (e η))
  let F' : StalkT f e s ≃ₗ[(Spec (CommRingCat.of R₀)).presheaf.stalk s]
      ((Spec (CommRingCat.of R₀)).presheaf.stalk s) ⊗[Γ(X, U)] Ω[Γ(X, U)⁄R₀] :=
    (TensorProduct.AlgebraTensorModule.congr
        (LinearEquiv.refl ((Spec (CommRingCat.of R₀)).presheaf.stalk s)
          ((Spec (CommRingCat.of R₀)).presheaf.stalk s)) E1.symm).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange Γ(X, U) (X.presheaf.stalk (e s))
        ((Spec (CommRingCat.of R₀)).presheaf.stalk s)
        ((Spec (CommRingCat.of R₀)).presheaf.stalk s) Ω[Γ(X, U)⁄R₀])
  let F : GenT f e (η := η) ≃ₗ[(Spec (CommRingCat.of R₀)).presheaf.stalk η]
      ((Spec (CommRingCat.of R₀)).presheaf.stalk η) ⊗[Γ(X, U)] Ω[Γ(X, U)⁄R₀] :=
    (TensorProduct.AlgebraTensorModule.congr
        (LinearEquiv.refl ((Spec (CommRingCat.of R₀)).presheaf.stalk η)
          ((Spec (CommRingCat.of R₀)).presheaf.stalk η)) E2.symm).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange Γ(X, U) (X.presheaf.stalk (e η))
        ((Spec (CommRingCat.of R₀)).presheaf.stalk η)
        ((Spec (CommRingCat.of R₀)).presheaf.stalk η) Ω[Γ(X, U)⁄R₀])
  let C := TensorProduct.AlgebraTensorModule.cancelBaseChange Γ(X, U)
    ((Spec (CommRingCat.of R₀)).presheaf.stalk s) ((Spec (CommRingCat.of R₀)).presheaf.stalk η)
    ((Spec (CommRingCat.of R₀)).presheaf.stalk η) Ω[Γ(X, U)⁄R₀]
  let G := ((TensorProduct.AlgebraTensorModule.congr
      (LinearEquiv.refl ((Spec (CommRingCat.of R₀)).presheaf.stalk η)
        ((Spec (CommRingCat.of R₀)).presheaf.stalk η)) F').trans C).trans F.symm
  have hE1 : ∀ a : Γ(X, U), E1.symm (D R₀ _ (algebraMap Γ(X, U) (X.presheaf.stalk (e s)) a)) =
      1 ⊗ₜ D R₀ _ a := fun a => tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap _ _ _ a
  have hE2 : ∀ a : Γ(X, U), E2.symm (D R₀ _ (algebraMap Γ(X, U) (X.presheaf.stalk (e η)) a)) =
      1 ⊗ₜ D R₀ _ a := fun a => tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap _ _ _ a
  have hF'sym : ∀ (r : (Spec (CommRingCat.of R₀)).presheaf.stalk s) (a : Γ(X, U)),
      F'.symm (r ⊗ₜ D R₀ _ a) =
        r ⊗ₜ D R₀ _ (algebraMap Γ(X, U) (X.presheaf.stalk (e s)) a) := by
    intro r a
    rw [LinearEquiv.symm_apply_eq]
    change _ = TensorProduct.AlgebraTensorModule.cancelBaseChange _ _ _ _ _
      (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl _ _) E1.symm
        (r ⊗ₜ D R₀ _ (algebraMap Γ(X, U) (X.presheaf.stalk (e s)) a)))
    rw [TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply, hE1,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]
  have key : ∀ y, F (stalkToGeneric f e hη s (F'.symm y)) = C (1 ⊗ₜ y) := by
    intro y
    induction y using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy, TensorProduct.tmul_add]
    | tmul r ω =>
      have hω : ω ∈ Submodule.span Γ(X, U) (Set.range (D R₀ Γ(X, U))) := by
        rw [span_range_derivation]; trivial
      induction hω using Submodule.span_induction generalizing r with
      | mem z hz =>
        obtain ⟨a, rfl⟩ := hz
        rw [hF'sym, stalkToGeneric_tmul]
        change F (sig hη s r ⊗ₜ KaehlerDifferential.map R₀ R₀ (X.presheaf.stalk (e s))
          (X.presheaf.stalk (e η)) (D R₀ _ _)) = _
        rw [KaehlerDifferential.map_D, ← IsScalarTower.algebraMap_apply]
        change TensorProduct.AlgebraTensorModule.cancelBaseChange _ _ _ _ _
          (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl _ _) E2.symm
            (sig hη s r ⊗ₜ D R₀ _ (algebraMap Γ(X, U) (X.presheaf.stalk (e η)) a))) = _
        rw [TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply, hE2,
          TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul,
          TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, Algebra.smul_def, mul_one]
        rfl
      | zero => simp only [TensorProduct.tmul_zero, map_zero]
      | add x y _ _ hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
      | smul b x _ hx => rw [← TensorProduct.smul_tmul, hx, TensorProduct.smul_tmul]
  refine ⟨G, fun m => ?_, Module.Projective.of_equiv F'.symm⟩
  apply F.injective
  change F (F.symm (C (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl _ _) F'
    (1 ⊗ₜ m)))) = _
  rw [LinearEquiv.apply_symm_apply, TensorProduct.AlgebraTensorModule.congr_tmul,
    LinearEquiv.refl_apply, ← key, LinearEquiv.symm_apply_apply]

/-- `⋀^n` of a linear equivalence is injective. -/
theorem wedgeMap_equiv_injective {A : Type*} [CommRing A] {M N : Type*} [AddCommGroup M]
    [Module A M] [AddCommGroup N] [Module A N] (E : M ≃ₗ[A] N) :
    Function.Injective (wedgeMap (RingHom.id A) n E.toLinearMap) := by
  intro x y hxy
  have h : ∀ z, wedgeMap (RingHom.id A) n E.symm.toLinearMap
      (wedgeMap (RingHom.id A) n E.toLinearMap z) = z := fun z => by
    rw [wedgeMap_comp_apply (RingHom.id A) n (RingHom.id A) (RingHom.id A) rfl E.toLinearMap
      E.symm.toLinearMap LinearMap.id (fun x => E.symm_apply_apply x)]
    exact wedgeMap_apply_eq_self n _ rfl _ (fun x => rfl) z
  rw [← h x, ← h y, hxy]

/-- Two composites of `⋀^n` of semilinear maps agree when the composites agree on `M` and
on the scalars. -/
theorem wedgeMap_comp_eq {A B₁ B₂ C : Type*} [CommRing A] [CommRing B₁] [CommRing B₂]
    [CommRing C] (g₁ : A →+* B₁) (g₂ : A →+* B₂) (ψ₁ : B₁ →+* C) (ψ₂ : B₂ →+* C)
    (hring : ∀ a, ψ₁ (g₁ a) = ψ₂ (g₂ a)) {M N₁ N₂ P : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N₁] [Module B₁ N₁] [AddCommGroup N₂] [Module B₂ N₂] [AddCommGroup P]
    [Module C P] (u₁ : M →ₛₗ[g₁] N₁) (u₂ : M →ₛₗ[g₂] N₂) (v₁ : N₁ →ₛₗ[ψ₁] P)
    (v₂ : N₂ →ₛₗ[ψ₂] P) (h : ∀ m, v₁ (u₁ m) = v₂ (u₂ m)) (ω : ⋀[A]^n M) :
    wedgeMap ψ₁ n v₁ (wedgeMap g₁ n u₁ ω) = wedgeMap ψ₂ n v₂ (wedgeMap g₂ n u₂ ω) := by
  let w : M →ₛₗ[ψ₁.comp g₁] P :=
    { toFun := fun m => v₁ (u₁ m)
      map_add' := fun a b => by simp only [map_add]
      map_smul' := fun a m => by
        rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ]
        rfl }
  rw [wedgeMap_comp_apply g₁ n ψ₁ (ψ₁.comp g₁) rfl u₁ v₁ w (fun _ => rfl),
    wedgeMap_comp_apply g₂ n ψ₂ (ψ₁.comp g₁) (RingHom.ext fun a => (hring a).symm) u₂ v₂ w
      (fun m => (h m).symm)]

/-- The abstract form of the injectivity: a semilinear map `φ : M → N` along an injective
`A → B`, with `M` projective and `N` the base change of `M` through `φ`, induces an injective
map `⋀^n M → ⋀^n N`. -/
theorem wedgeMap_injective_of_baseChange {A B M N : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]
    [Module.Projective A M] (φ : M →ₛₗ[algebraMap A B] N) (G : B ⊗[A] M ≃ₗ[B] N)
    (hG : ∀ m, G (1 ⊗ₜ m) = φ m) (hσ : Function.Injective (algebraMap A B)) :
    Function.Injective (wedgeMap (algebraMap A B) n φ) := by
  haveI := exteriorPower_flat_of_projective A M n
  have hT := exteriorPowerToBaseChange_injective_of_flat A B M n hσ
  have hsplit : ∀ ω, wedgeMap (algebraMap A B) n φ ω = wedgeMap (RingHom.id B) n G.toLinearMap
      (exteriorPowerToBaseChange A B M n ω) := by
    intro ω
    have hω : ω ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A n)) := by
      rw [exteriorPower.ιMulti_span]; trivial
    induction hω using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨m, rfl⟩ := hz
      rw [exteriorPowerToBaseChange_ιMulti, wedgeMap_ιMulti, wedgeMap_ιMulti]
      exact congrArg _ (funext fun i => (hG (m i)).symm)
    | zero => simp only [map_zero]
    | add x y _ _ hx hy => simp only [map_add, hx, hy]
    | smul r x _ hx =>
      rw [LinearMap.map_smulₛₗ, hx, LinearMap.map_smul, ← algebraMap_smul B r,
        LinearMap.map_smulₛₗ]
      rfl
  intro x y hxy
  rw [hsplit, hsplit] at hxy
  exact hT (wedgeMap_equiv_injective n G hxy)

/-- **`⋀^n` of the stalk injects into `⋀^n` of the generic fibre.** -/
theorem wedgeGen_injective [Smooth f] (hσ : Function.Injective (sig hη s)) :
    Function.Injective (wedgeGen f e hη s n) := by
  letI := algSt f (e s)
  letI := algBO e s
  letI := algSt f (e η)
  letI := algBO e η
  letI := algOEta hη s
  obtain ⟨G, hG, hP⟩ := exists_baseChange f e hη s
  haveI := hP
  exact wedgeMap_injective_of_baseChange n (stalkToGenericₛₗ f e hη s) G hG hσ

end Wedge

/-! ## Stalks of `⋀^n` on a scheme: germs and scalars -/

section SchemeWedge

variable {Y : Scheme.{u}} (M : PresheafOfModulesOfCommRing Y.presheaf) (n : ℕ)

/-- The image in the sheaf `⋀^n M` of a section of the presheaf `U ↦ ⋀^n M(U)`. -/
noncomputable def wedgeUnit (U : Y.Opens) (ω : ⋀[Γ(Y, U)]^n (M.obj (op U))) :
    Γ(schemeWedge M n, U) :=
  ((PresheafOfModules.toPresheaf _).map
    (@toWedgeSheaf _ _ _ Y.presheaf Y.ringCatSheaf (𝟙 _) isLocallyInjective_ringCatSheaf
      isLocallySurjective_ringCatSheaf _ _ M n)).app (op U) ω

/-- Every element of a stalk of `⋀^n M` is the germ of the image of a section of the presheaf
`U ↦ ⋀^n M(U)`, over an open inside any given neighbourhood. -/
theorem schemeWedge_exists_germ (x : Y) (V : Y.Opens) (hV : x ∈ V)
    (y : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := Y.toPresheafedSpace)
      (schemeWedge M n).val.presheaf x) :
    ∃ (U : Y.Opens) (_ : U ≤ V) (hx : x ∈ U) (ω : ⋀[Γ(Y, U)]^n (M.obj (op U))),
      TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := Y.toPresheafedSpace)
        (schemeWedge M n).val.presheaf U x hx (wedgeUnit M n U ω) = y := by
  haveI := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u}
    (wedgePresheaf M n).presheaf
  obtain ⟨z, hz⟩ := (ConcreteCategory.bijective_of_isIso
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (toSheafify (Opens.grothendieckTopology Y) (wedgePresheaf M n).presheaf))).2 y
  obtain ⟨U₀, hx₀, ω₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq (wedgePresheaf M n).presheaf z
  have hxW : x ∈ U₀ ⊓ V := ⟨hx₀, hV⟩
  let ω := wedgeRes M n (homOfLE (inf_le_left : U₀ ⊓ V ≤ U₀)).op ω₀
  refine ⟨U₀ ⊓ V, inf_le_right, hxW, ω, ?_⟩
  have e1 : TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (wedgePresheaf M n).presheaf
      (U₀ ⊓ V) x hxW ω = TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (wedgePresheaf M n).presheaf U₀ x hx₀ ω₀ :=
    wedgeStalkGerm_res M n x (homOfLE inf_le_left) hxW ω₀
  rw [← hz, ← e1]
  have h := TopCat.Presheaf.stalkFunctor_map_germ_apply (U₀ ⊓ V) x hxW
    (toSheafify (Opens.grothendieckTopology Y) (wedgePresheaf M n).presheaf) ω
  erw [h]
  unfold wedgeUnit
  rw [@toPresheaf_map_toWedgeSheaf _ Y.presheaf Y.ringCatSheaf (𝟙 _)
    isLocallyInjective_ringCatSheaf isLocallySurjective_ringCatSheaf M n]
  rfl

/-- The stalk equivalence on the germ of the image of a section. -/
theorem schemeWedgeStalkEquiv_wedgeUnit (x : Y) (U : Y.Opens) (hx : x ∈ U)
    (ω : ⋀[Γ(Y, U)]^n (M.obj (op U))) :
    schemeWedgeStalkEquiv M n x
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := Y.toPresheafedSpace)
          (schemeWedge M n).val.presheaf U x hx (wedgeUnit M n U ω)) =
      wedgeGerm M n x U hx ω :=
  schemeWedgeStalkEquiv_germ M n x U hx ω

/-- The image of a section is linear. -/
theorem wedgeUnit_smul (U : Y.Opens) (c : Γ(Y, U)) (ω : ⋀[Γ(Y, U)]^n (M.obj (op U))) :
    wedgeUnit M n U (c • ω) = c • wedgeUnit M n U ω :=
  ((@toWedgeSheaf _ _ _ Y.presheaf Y.ringCatSheaf (𝟙 _) isLocallyInjective_ringCatSheaf
      isLocallySurjective_ringCatSheaf _ _ M n).app (op U)).hom.map_smul c ω

/-- **The stalk equivalence of `⋀^n M` is linear** over the local ring. -/
theorem schemeWedgeStalkEquiv_smul (x : Y) (r : Y.presheaf.stalk x)
    (y : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := Y.toPresheafedSpace)
      (schemeWedge M n).val.presheaf x) :
    schemeWedgeStalkEquiv M n x (r • y) = r • schemeWedgeStalkEquiv M n x y := by
  obtain ⟨V, hV, c, rfl⟩ := TopCat.Presheaf.exists_germ_eq Y.presheaf r
  obtain ⟨U, hUV, hx, ω, rfl⟩ := schemeWedge_exists_germ M n x V hV y
  have hc : (Y.presheaf.germ V x hV).hom c =
      (Y.presheaf.germ U x hx).hom (Y.presheaf.map (homOfLE hUV).op c) :=
    (TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE hUV) x hx c).symm
  rw [hc]
  have e1 := stalk_germ_smul (schemeWedge M n) x U hx (Y.presheaf.map (homOfLE hUV).op c)
    (wedgeUnit M n U ω)
  rw [← wedgeUnit_smul] at e1
  erw [← e1]
  rw [schemeWedgeStalkEquiv_wedgeUnit, schemeWedgeStalkEquiv_wedgeUnit, LinearMap.map_smulₛₗ]

end SchemeWedge

/-! ## The sheaf `⋀^n e*Ω¹` and its generic germ -/

section Top

variable {R₀ : Type u} [CommRing R₀] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R₀))
  (e : Spec (CommRingCat.of R₀) ⟶ X) {η : Spec (CommRingCat.of R₀)} (hη : ∀ s, η ⤳ s)
  (n : ℕ)

/-- `e*Ω¹` as a presheaf of modules over the structure presheaf of commutative rings. -/
noncomputable abbrev pullPre : PresheafOfModulesOfCommRing (Spec (CommRingCat.of R₀)).presheaf :=
  (pullOmega f e).val

/-- **The sheaf `⋀^n e*Ω¹_{X/R₀}` on `Spec R₀`**: the sheafification of
`V ↦ ⋀^n_{𝒪(V)} Γ(V, e*Ω¹)`. -/
noncomputable abbrev pullOmegaTop : (Spec (CommRingCat.of R₀)).Modules :=
  schemeWedge (pullPre f e) n

/-- The map `phi s` from the stalk of `e*Ω¹` to the generic fibre, semilinear along `σ`. -/
noncomputable def phiₛₗ (s : Spec (CommRingCat.of R₀)) :
    letI := algSt f (e η)
    letI := algBO e η
    TopCat.Presheaf.stalk (C := Ab.{u}) (pullOmega f e).val.presheaf s →ₛₗ[sig hη s]
      GenT f e (η := η) :=
  letI := algSt f (e η)
  letI := algBO e η
  { toFun := phi f e hη s
    map_add' := map_add _
    map_smul' := phi_smul f e hη s }

theorem phiₛₗ_apply (s : Spec (CommRingCat.of R₀))
    (m : TopCat.Presheaf.stalk (C := Ab.{u}) (pullOmega f e).val.presheaf s) :
    phiₛₗ f e hη s m = phi f e hη s m := rfl

/-- **The map from the stalk of `⋀^n e*Ω¹` at `s` to `⋀^n` of the generic fibre**: the stalk
equivalence followed by `⋀^n` of `phi s`. -/
noncomputable def rhoTop (s : Spec (CommRingCat.of R₀)) :
    letI := algSt f (e η)
    letI := algBO e η
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (X := (Spec (CommRingCat.of R₀)).toPresheafedSpace)
        (pullOmegaTop f e n).val.presheaf s →+
      ⋀[(Spec (CommRingCat.of R₀)).presheaf.stalk η]^n (GenT f e (η := η)) :=
  letI := algSt f (e η)
  letI := algBO e η
  (wedgeMap (sig hη s) n (phiₛₗ f e hη s)).toAddMonoidHom.comp
    (schemeWedgeStalkEquiv (pullPre f e) n s).toAddMonoidHom

theorem rhoTop_apply (s : Spec (CommRingCat.of R₀))
    (y : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (X := (Spec (CommRingCat.of R₀)).toPresheafedSpace) (pullOmegaTop f e n).val.presheaf s) :
    rhoTop f e hη n s y =
      wedgeMap (sig hη s) n (phiₛₗ f e hη s) (schemeWedgeStalkEquiv (pullPre f e) n s y) :=
  rfl

/-- The maps at `η` and at `s` agree on the image of a section of the presheaf. -/
theorem wedgeMap_phi_wedgeGerm (s : Spec (CommRingCat.of R₀))
    (U : (Spec (CommRingCat.of R₀)).Opens) (hs : s ∈ U)
    (ω : ⋀[Γ(Spec (CommRingCat.of R₀), U)]^n ((pullPre f e).obj (op U))) :
    wedgeMap (sig hη η) n (phiₛₗ f e hη η)
        (wedgeGerm (pullPre f e) n η U ((hη s).mem_open U.isOpen hs) ω) =
      wedgeMap (sig hη s) n (phiₛₗ f e hη s) (wedgeGerm (pullPre f e) n s U hs ω) := by
  have hring : ∀ c : Γ(Spec (CommRingCat.of R₀), U),
      sig hη η (((Spec (CommRingCat.of R₀)).presheaf.germ U η
        ((hη s).mem_open U.isOpen hs)).hom c) =
      sig hη s (((Spec (CommRingCat.of R₀)).presheaf.germ U s hs).hom c) := fun c => by
    rw [sig_self]
    exact (TopCat.Presheaf.germ_stalkSpecializes_apply _ hs (hη s) c).symm
  have hm : ∀ m : (pullPre f e).obj (op U),
      phiₛₗ f e hη η (germₛₗ (pullPre f e) η U ((hη s).mem_open U.isOpen hs) m) =
        phiₛₗ f e hη s (germₛₗ (pullPre f e) s U hs m) := fun m => by
    have h1 := phi_modSpec f e hη s (germₛₗ (pullPre f e) s U hs m)
    have h2 := modSpec_germ (pullOmega f e) (hη s) U hs m
    exact (congrArg (phi f e hη η) h2.symm).trans h1
  exact wedgeMap_comp_eq n _ _ _ _ hring _ _ _ _ hm ω

/-- **The maps to the generic fibre commute with specialization.** -/
theorem rhoTop_modSpec (s : Spec (CommRingCat.of R₀))
    (y : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (X := (Spec (CommRingCat.of R₀)).toPresheafedSpace) (pullOmegaTop f e n).val.presheaf s) :
    rhoTop f e hη n η (modSpec (pullOmegaTop f e n) (hη s) y) = rhoTop f e hη n s y := by
  obtain ⟨U, -, hs, ω, rfl⟩ := schemeWedge_exists_germ (pullPre f e) n s ⊤ trivial y
  have hg := modSpec_germ (pullOmegaTop f e n) (hη s) U hs (wedgeUnit (pullPre f e) n U ω)
  have e1 := schemeWedgeStalkEquiv_wedgeUnit (pullPre f e) n η U ((hη s).mem_open U.isOpen hs) ω
  have e2 := schemeWedgeStalkEquiv_wedgeUnit (pullPre f e) n s U hs ω
  refine (congrArg (rhoTop f e hη n η) hg).trans ?_
  refine (congrArg (wedgeMap (sig hη η) n (phiₛₗ f e hη η)) e1).trans ?_
  refine Eq.trans ?_ (congrArg (wedgeMap (sig hη s) n (phiₛₗ f e hη s)) e2).symm
  exact wedgeMap_phi_wedgeGerm f e hη n s U hs ω

/-- The map from a stalk is semilinear along `σ`. -/
theorem rhoTop_smul (s : Spec (CommRingCat.of R₀)) (r : (Spec (CommRingCat.of R₀)).presheaf.stalk s)
    (y : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (X := (Spec (CommRingCat.of R₀)).toPresheafedSpace) (pullOmegaTop f e n).val.presheaf s) :
    letI := algSt f (e η)
    letI := algBO e η
    rhoTop f e hη n s (r • y) = sig hη s r • rhoTop f e hη n s y := by
  letI := algSt f (e η)
  letI := algBO e η
  have e2 := schemeWedgeStalkEquiv_smul (pullPre f e) n s r y
  refine (congrArg (wedgeMap (sig hη s) n (phiₛₗ f e hη s)) e2).trans ?_
  exact (wedgeMap (sig hη s) n (phiₛₗ f e hη s)).map_smulₛₗ _ _

/-- The inverse stalk equivalence is linear. -/
theorem schemeWedgeStalkEquiv_symm_smul (s : Spec (CommRingCat.of R₀))
    (r : (Spec (CommRingCat.of R₀)).presheaf.stalk s)
    (ω : ⋀[(Spec (CommRingCat.of R₀)).presheaf.stalk s]^n
      (TopCat.Presheaf.stalk (C := Ab.{u}) (pullOmega f e).val.presheaf s)) :
    (schemeWedgeStalkEquiv (pullPre f e) n s).symm (r • ω) =
      r • (schemeWedgeStalkEquiv (pullPre f e) n s).symm ω := by
  apply (schemeWedgeStalkEquiv (pullPre f e) n s).injective
  refine ((schemeWedgeStalkEquiv (pullPre f e) n s).apply_symm_apply (r • ω)).trans ?_
  refine Eq.trans ?_ (schemeWedgeStalkEquiv_smul (pullPre f e) n s r _).symm
  exact congrArg (r • ·) ((schemeWedgeStalkEquiv (pullPre f e) n s).apply_symm_apply ω).symm

/-- The value of the map from a stalk on a wedge of germs. -/
theorem rhoTop_symm_ιMulti (s : Spec (CommRingCat.of R₀))
    (m : Fin n → TopCat.Presheaf.stalk (C := Ab.{u}) (pullOmega f e).val.presheaf s) :
    letI := algSt f (e η)
    letI := algBO e η
    rhoTop f e hη n s ((schemeWedgeStalkEquiv (pullPre f e) n s).symm
        (exteriorPower.ιMulti _ n m)) =
      exteriorPower.ιMulti _ n (fun i => phi f e hη s (m i)) := by
  letI := algSt f (e η)
  letI := algBO e η
  rw [rhoTop_apply, AddEquiv.apply_symm_apply]
  exact wedgeMap_ιMulti _ n _ m

/-- `⋀^n` of `phi s` is `wedgeGen s` after `⋀^n` of the stalk formula. -/
theorem wedgeMap_phi_eq (s : Spec (CommRingCat.of R₀))
    (ω : ⋀[(Spec (CommRingCat.of R₀)).presheaf.stalk s]^n
      (TopCat.Presheaf.stalk (C := Ab.{u}) (pullOmega f e).val.presheaf s)) :
    letI := algSt f (e s)
    letI := algBO e s
    wedgeMap (sig hη s) n (phiₛₗ f e hη s) ω =
      wedgeGen f e hη s n (wedgeMap (RingHom.id _) n (pullStalkEquiv f e s).toLinearMap ω) := by
  letI := algSt f (e s)
  letI := algBO e s
  letI := algSt f (e η)
  letI := algBO e η
  exact (wedgeMap_comp_apply (RingHom.id _) n (sig hη s) (sig hη s) (RingHom.comp_id _)
    (pullStalkEquiv f e s).toLinearMap (stalkToGenericₛₗ f e hη s) (phiₛₗ f e hη s)
    (fun _ => rfl) ω).symm

/-- **The stalks of `⋀^n e*Ω¹` inject into `⋀^n` of the generic fibre.** -/
theorem rhoTop_injective [Smooth f] (hσ : ∀ s, Function.Injective (sig hη s))
    (s : Spec (CommRingCat.of R₀)) : Function.Injective (rhoTop f e hη n s) := by
  intro x y hxy
  have h1 := wedgeMap_phi_eq f e hη n s (schemeWedgeStalkEquiv (pullPre f e) n s x)
  have h2 := wedgeMap_phi_eq f e hη n s (schemeWedgeStalkEquiv (pullPre f e) n s y)
  exact (schemeWedgeStalkEquiv (pullPre f e) n s).injective
    (wedgeMap_equiv_injective n _ (wedgeGen_injective f e hη s n (hσ s)
      (h1.symm.trans (hxy.trans h2))))

theorem modSpecTop_injective [Smooth f] (hσ : ∀ s, Function.Injective (sig hη s))
    (s : Spec (CommRingCat.of R₀)) :
    Function.Injective (modSpec (pullOmegaTop f e n) (hη s)) := fun a b hab => by
  have h := congrArg (rhoTop f e hη n η) hab
  rw [rhoTop_modSpec, rhoTop_modSpec] at h
  exact rhoTop_injective f e hη n hσ s h

/-- The underlying sheaf of abelian groups of `⋀^n e*Ω¹`. -/
noncomputable def topAbSheaf : TopCat.Sheaf Ab.{u} (Spec (CommRingCat.of R₀)) :=
  ⟨(Scheme.Modules.toPresheaf _).obj (pullOmegaTop f e n), (pullOmegaTop f e n).isSheaf⟩

/-- **The generic germ of `⋀^n e*Ω¹`**: global sections to `⋀^n` of the generic fibre. -/
noncomputable def genericGermTop :
    letI := algSt f (e η)
    letI := algBO e η
    Γ(pullOmegaTop f e n, ⊤) →+
      ⋀[(Spec (CommRingCat.of R₀)).presheaf.stalk η]^n (GenT f e (η := η)) :=
  (rhoTop f e hη n η).comp
    (TopCat.Presheaf.germ (pullOmegaTop f e n).val.presheaf ⊤ η trivial).hom

/-- **The generic germ of `⋀^n e*Ω¹` is injective.** -/
theorem genericGermTop_injective [Smooth f] (hσ : ∀ s, Function.Injective (sig hη s)) :
    Function.Injective (genericGermTop f e hη n) := by
  have hg := germ_injective_of_specializes (topAbSheaf f e n) (U := ⊤) (η := η) trivial
    (fun s _ => hη s) (fun s _ => modSpecTop_injective f e hη n hσ s)
  exact (rhoTop_injective f e hη n hσ η).comp hg

/-- **The image of the generic germ of `⋀^n e*Ω¹` is the intersection of the images of the
stalks.** -/
theorem range_genericGermTop [Smooth f] (hσ : ∀ s, Function.Injective (sig hη s)) :
    Set.range (genericGermTop f e hη n) = ⋂ s, Set.range (rhoTop f e hη n s) := by
  have hR := range_germ_eq_iInter_specializes (topAbSheaf f e n) (U := ⊤) (η := η) trivial
    (fun s _ => hη s) (fun s _ => modSpecTop_injective f e hη n hσ s)
  ext v
  simp only [Set.mem_iInter, Set.mem_range]
  constructor
  · rintro ⟨σ, rfl⟩ s
    refine ⟨TopCat.Presheaf.germ (pullOmegaTop f e n).val.presheaf ⊤ s trivial σ, ?_⟩
    rw [← rhoTop_modSpec]
    exact congrArg (rhoTop f e hη n η) (modSpec_germ (pullOmegaTop f e n) (hη s) ⊤ trivial σ)
  · intro hv
    choose w hw using hv
    have hmem : w η ∈ Set.range
        (ConcreteCategory.hom ((topAbSheaf f e n).presheaf.germ ⊤ η trivial)) := by
      rw [hR]
      exact Set.mem_iInter₂.2 fun s _ => ⟨w s, rhoTop_injective f e hη n hσ η
        ((rhoTop_modSpec f e hη n s (w s)).trans ((hw s).trans (hw η).symm))⟩
    obtain ⟨σ, hσ'⟩ := hmem
    refine ⟨σ, ?_⟩
    change rhoTop f e hη n η _ = v
    exact (congrArg (rhoTop f e hη n η) hσ').trans (hw η)

/-- The generic germ is linear over `Γ(S, 𝒪_S) → 𝒪_{S,η}`. -/
theorem genericGermTop_smul (c : Γ(Spec (CommRingCat.of R₀), ⊤)) (m : Γ(pullOmegaTop f e n, ⊤)) :
    letI := algSt f (e η)
    letI := algBO e η
    genericGermTop f e hη n (c • m) =
      ((Spec (CommRingCat.of R₀)).presheaf.germ ⊤ η trivial).hom c • genericGermTop f e hη n m := by
  letI := algSt f (e η)
  letI := algBO e η
  have e1 := stalk_germ_smul (pullOmegaTop f e n) η ⊤ trivial c m
  have e2 := schemeWedgeStalkEquiv_smul (pullPre f e) n η
    (((Spec (CommRingCat.of R₀)).presheaf.germ ⊤ η trivial).hom c)
    (TopCat.Presheaf.germ (pullOmegaTop f e n).val.presheaf ⊤ η trivial m)
  refine (congrArg (rhoTop f e hη n η) e1).trans ?_
  refine (congrArg (wedgeMap (sig hη η) n (phiₛₗ f e hη η)) e2).trans ?_
  refine ((wedgeMap (sig hη η) n (phiₛₗ f e hη η)).map_smulₛₗ _ _).trans ?_
  exact congrArg (· • genericGermTop f e hη n m) (sig_self hη _)

end Top

/-! ## Landing in a Hodge line `K ⊗_R ⋀^n_R V` -/

section Hodge

variable {R K E B V W : Type*} [CommRing R] [CommRing K] [CommRing E] [CommRing B]
  [Algebra R K] [Algebra R E] [Algebra R B] [Algebra B E] [IsScalarTower R B E]
  [AddCommGroup V] [Module B V] [Module R V] [IsScalarTower R B V]
  [AddCommGroup W] [Module E W] [Module B W] [IsScalarTower B E W]
  (κ : E ≃ₐ[R] K) (θ : V ≃ₗ[B] W) (hsurj : Function.Surjective (algebraMap B E)) (n : ℕ)
  (hwedge : ∀ (x : B) (v : Fin n → V) (i : Fin n),
    κ (algebraMap B E x) • ((1 : K) ⊗ₜ[R] exteriorPower.ιMulti R n v) =
      (1 : K) ⊗ₜ[R] exteriorPower.ιMulti R n (Function.update v i (x • v i)))

/-- `E` acts on `K ⊗_R ⋀^n_R V` through `κ : E ≃ K`. -/
noncomputable abbrev hodgeModule : Module E (K ⊗[R] ⋀[R]^n V) :=
  Module.compHom (K ⊗[R] ⋀[R]^n V) (κ : E →+* K)

include hwedge in
theorem hodge_smul_aux [d : DecidableEq (Fin n)] (x : B) (u : Fin n → V) (i : Fin n) (b : V) :
    (1 : K) ⊗ₜ[R] exteriorPower.ιMulti R n (Function.update u i (x • b)) =
      (κ : E →+* K) (algebraMap B E x) •
        ((1 : K) ⊗ₜ[R] exteriorPower.ιMulti R n (Function.update u i b)) := by
  obtain rfl : d = instDecidableEqFin n := Subsingleton.elim _ _
  have h := hwedge x (Function.update u i b) i
  rw [Function.update_self, Function.update_idem] at h
  exact h.symm

include θ hsurj hwedge in
/-- The `E`-alternating map `(w₁, …, wₙ) ↦ 1 ⊗ θ⁻¹ w₁ ∧ ⋯ ∧ θ⁻¹ wₙ`, given the wedge identity
`κ(x) • (1 ⊗ v₁ ∧ ⋯ ∧ vₙ) = 1 ⊗ v₁ ∧ ⋯ ∧ x vᵢ ∧ ⋯ ∧ vₙ`. -/
noncomputable def hodgeAlt :
    letI := hodgeModule (V := V) κ n
    W [⋀^Fin n]→ₗ[E] K ⊗[R] ⋀[R]^n V :=
  letI := hodgeModule (V := V) κ n
  { toFun := fun w => (1 : K) ⊗ₜ[R] exteriorPower.ιMulti R n (fun i => θ.symm (w i))
    map_update_add' := fun w i a b => by
      simp only [fun_update_eq, map_add, AlternatingMap.map_update_add, TensorProduct.tmul_add]
    map_update_smul' := fun w i r a => by
      obtain ⟨x, rfl⟩ := hsurj r
      have h1 : (algebraMap B E x) • a = x • a := algebraMap_smul E x a
      change (1 : K) ⊗ₜ[R] exteriorPower.ιMulti R n
          (fun j => θ.symm (Function.update w i (algebraMap B E x • a) j)) =
        (κ : E →+* K) (algebraMap B E x) •
          ((1 : K) ⊗ₜ[R] exteriorPower.ιMulti R n (fun j => θ.symm (Function.update w i a j)))
      rw [h1, fun_update_eq, fun_update_eq, LinearEquiv.map_smul]
      exact hodge_smul_aux (V := V) κ n hwedge x (fun j => θ.symm (w j)) i (θ.symm a)
    map_eq_zero_of_eq' := fun w i j h hij => by
      rw [(exteriorPower.ιMulti R n).map_eq_zero_of_eq _ (by simp only [h]) hij,
        TensorProduct.tmul_zero] }

include θ hsurj hwedge in
/-- **The map to the Hodge line**: `⋀^n_E W → K ⊗_R ⋀^n_R V`, `w₁ ∧ ⋯ ∧ wₙ ↦
1 ⊗ θ⁻¹ w₁ ∧ ⋯ ∧ θ⁻¹ wₙ`, linear over `E` acting through `κ`. -/
noncomputable def toHodge :
    letI := hodgeModule (V := V) κ n
    ⋀[E]^n W →ₗ[E] K ⊗[R] ⋀[R]^n V :=
  letI := hodgeModule (V := V) κ n
  exteriorPower.alternatingMapLinearEquiv (hodgeAlt κ θ hsurj n hwedge)

include hsurj hwedge in
theorem toHodge_ιMulti (w : Fin n → W) :
    toHodge κ θ hsurj n hwedge (exteriorPower.ιMulti E n w) =
      (1 : K) ⊗ₜ[R] exteriorPower.ιMulti R n (fun i => θ.symm (w i)) :=
  letI := hodgeModule (V := V) κ n
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

include hsurj hwedge in
theorem toHodge_smul (r : E) (y : ⋀[E]^n W) :
    toHodge κ θ hsurj n hwedge (r • y) = κ r • toHodge κ θ hsurj n hwedge y :=
  letI := hodgeModule (V := V) κ n
  (toHodge κ θ hsurj n hwedge).map_smul r y

/-- `θ` as a map semilinear along `R → E`. -/
noncomputable def thetaₛₗ : V →ₛₗ[algebraMap R E] W where
  toFun v := θ v
  map_add' := map_add θ
  map_smul' a v := by
    change θ (a • v) = algebraMap R E a • θ v
    rw [← algebraMap_smul B a v, LinearEquiv.map_smul, IsScalarTower.algebraMap_apply R B E,
      algebraMap_smul E (algebraMap R B a) (θ v)]

/-- A left inverse of `toHodge`: `l ⊗ (v₁ ∧ ⋯ ∧ vₙ) ↦ κ⁻¹(l) • θ v₁ ∧ ⋯ ∧ θ vₙ`. -/
noncomputable def fromHodge : K ⊗[R] ⋀[R]^n V →+ ⋀[E]^n W :=
  TensorProduct.liftAddHom
    { toFun := fun l =>
        { toFun := fun ω => κ.symm l • wedgeMap (algebraMap R E) n (thetaₛₗ θ) ω
          map_zero' := by simp only [map_zero, smul_zero]
          map_add' := fun a b => by simp only [map_add, smul_add] }
      map_zero' := by ext; simp only [map_zero, zero_smul, AddMonoidHom.coe_mk,
        ZeroHom.coe_mk, AddMonoidHom.zero_apply]
      map_add' := fun a b => by ext; simp only [map_add, add_smul, AddMonoidHom.coe_mk,
        ZeroHom.coe_mk, AddMonoidHom.add_apply] }
    (fun r l ω => by
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rw [LinearMap.map_smulₛₗ, map_smul, smul_smul, Algebra.smul_def, mul_comm])

theorem fromHodge_tmul (l : K) (ω : ⋀[R]^n V) :
    fromHodge κ θ n (l ⊗ₜ ω) = κ.symm l • wedgeMap (algebraMap R E) n (thetaₛₗ θ) ω := rfl

theorem fromHodge_smul (l : K) (z : K ⊗[R] ⋀[R]^n V) :
    fromHodge κ θ n (l • z) = κ.symm l • fromHodge κ θ n z := by
  induction z using TensorProduct.inductionOn with
  | tmul a ω => rw [TensorProduct.smul_tmul', fromHodge_tmul, fromHodge_tmul, smul_eq_mul,
      map_mul, mul_smul]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

include hsurj hwedge in
theorem fromHodge_toHodge (y : ⋀[E]^n W) :
    fromHodge κ θ n (toHodge κ θ hsurj n hwedge y) = y := by
  have hy : y ∈ Submodule.span E (Set.range (exteriorPower.ιMulti E n)) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨w, rfl⟩ := hz
    rw [toHodge_ιMulti, fromHodge_tmul, map_one, one_smul, wedgeMap_ιMulti]
    exact congrArg _ (funext fun i => θ.apply_symm_apply (w i))
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul r x _ hx => rw [toHodge_smul, fromHodge_smul, AlgEquiv.symm_apply_apply, hx]

include hsurj hwedge in
/-- **The map to the Hodge line is injective.** -/
theorem toHodge_injective : Function.Injective (toHodge κ θ hsurj n hwedge) := fun x y h => by
  rw [← fromHodge_toHodge κ θ hsurj n hwedge x, ← fromHodge_toHodge κ θ hsurj n hwedge y, h]

end Hodge

/-! ## Two general facts used to identify the image -/

/-- If the image of `g` is the intersection of the images of the `ρ i`, the same holds after an
injective map `χ`. -/
theorem range_comp_eq_iInter {α β γ ι : Type*} {D : ι → Type*} (g : α → β)
    (ρ : ∀ i, D i → β) (hg : Set.range g = ⋂ i, Set.range (ρ i)) (χ : β → γ)
    (hχ : Function.Injective χ) [Nonempty ι] :
    Set.range (χ ∘ g) = ⋂ i, Set.range (χ ∘ ρ i) := by
  ext v
  simp only [Set.mem_iInter, Set.mem_range, Function.comp_apply]
  constructor
  · rintro ⟨a, rfl⟩ i
    have h : g a ∈ ⋂ i, Set.range (ρ i) := hg ▸ Set.mem_range_self a
    obtain ⟨y, hy⟩ := Set.mem_iInter.1 h i
    exact ⟨y, by rw [hy]⟩
  · intro hv
    choose y hy using hv
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    have hmem : ρ i₀ (y i₀) ∈ ⋂ i, Set.range (ρ i) :=
      Set.mem_iInter.2 fun i => ⟨y i, hχ ((hy i).trans (hy i₀).symm)⟩
    rw [← hg] at hmem
    obtain ⟨a, ha⟩ := hmem
    exact ⟨a, by rw [ha, hy]⟩

/-- An element with a multiple outside every maximal ideal in a submodule lies in it. -/
theorem mem_of_forall_maximal {R H : Type*} [CommRing R] [AddCommGroup H] [Module R H]
    (P : Submodule R H) (x : H) (h : ∀ M : Ideal R, M.IsMaximal → ∃ d ∉ M, d • x ∈ P) :
    x ∈ P := by
  let I : Ideal R :=
    { carrier := {d | d • x ∈ P}
      zero_mem' := by simp only [Set.mem_ofPred_eq, zero_smul]; exact P.zero_mem
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, add_smul] at *; exact P.add_mem ha hb
      smul_mem' := fun c a ha => by
        simp only [Set.mem_ofPred_eq, smul_eq_mul, mul_smul] at *; exact P.smul_mem c ha }
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hne
    obtain ⟨d, hd, hdx⟩ := h M hM
    exact hd (hIM hdx)
  have h1 : (1 : R) ∈ I := by rw [hI]; trivial
  have h2 : (1 : R) • x ∈ P := h1
  rwa [one_smul] at h2

/-- The index of `R x` in `M` is the index of `R φ(x)` in the image of an injective linear
map `φ`. -/
theorem relIndex_span_range {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (φ : M →ₗ[R] N) (hφ : Function.Injective φ) (x : M) :
    (Submodule.span R {φ x}).toAddSubgroup.relIndex (LinearMap.range φ).toAddSubgroup =
      (Submodule.span R {x}).toAddSubgroup.index := by
  have h1 : (Submodule.span R {φ x}).toAddSubgroup =
      (Submodule.span R {x}).toAddSubgroup.map (φ : M →+ N) := by
    rw [← Submodule.map_toAddSubgroup, Submodule.map_span, Set.image_singleton]
  have h2 : (LinearMap.range φ).toAddSubgroup = (⊤ : AddSubgroup M).map (φ : M →+ N) := by
    rw [LinearMap.range_eq_map, Submodule.map_toAddSubgroup, Submodule.top_toAddSubgroup]
  rw [h1, h2, AddSubgroup.relIndex_map_map_of_injective _ _
    (show Function.Injective (φ : M →+ N) from hφ),
    AddSubgroup.relIndex_top_right]

end GG

end ZInQ.HeightModelM5

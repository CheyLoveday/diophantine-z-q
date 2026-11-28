import ZInQKernel.Contrib.OneProof.HeightModelM5.StalkOmega
import ZInQKernel.Contrib.OneProof.HeightModelM5.IrreducibleSections

/-!
# The generic germ of the global sections of `e*Ω¹`

Let `f : X ⟶ Spec R₀` be a morphism of schemes, `e : Spec R₀ ⟶ X` a morphism, and `η` a point
of `Spec R₀` specializing to every point. For each `s`, the stalk of `e*Ω¹_{X/R₀}` at `s` is
`𝒪_{S,s} ⊗_{𝒪_{X,e(s)}} Ω[𝒪_{X,e(s)}⁄R₀]` (`pullStalkEquiv`, from the two stalk formulas), and
`stalkToGeneric s` sends it to the generic fibre `𝒪_{S,η} ⊗_{𝒪_{X,e(η)}} Ω[𝒪_{X,e(η)}⁄R₀]`,
`r ⊗ ω ↦ σ(r) ⊗ ω|_{e(η)}`.

* `phi_modSpec`: the map at `η` composed with the specialization of stalks is the map at `s`.
* `genericGerm`: global sections of `e*Ω¹` to the generic fibre (germ at `η`, then the map at
  `η`).
* `genericGerm_injective`, `range_genericGerm`: if every `stalkToGeneric s` is injective, then
  `genericGerm` is injective and its image is the intersection of the images of the
  `stalkToGeneric s`.

Everything here uses Mathlib and the sheaf constructions of this directory only.
-/

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace KaehlerDifferential
open scoped TensorProduct

set_option linter.style.haveILetI false

namespace ZInQ.HeightModelM5

/-! ## Specialization of stalks of a sheaf of modules -/

section ModSpec

variable {Y : Scheme.{u}} (M : Y.Modules) {y y' : Y} (h : y' ⤳ y)

/-- The specialization map of stalks of a sheaf of modules, as an additive map. -/
noncomputable def modSpec : TopCat.Presheaf.stalk (C := Ab.{u}) M.val.presheaf y →+
    TopCat.Presheaf.stalk (C := Ab.{u}) M.val.presheaf y' :=
  (TopCat.Presheaf.stalkSpecializes M.val.presheaf h).hom

lemma modSpec_germ (U : Y.Opens) (hy : y ∈ U) (a : Γ(M, U)) :
    modSpec M h (TopCat.Presheaf.germ M.val.presheaf U y hy a) =
      TopCat.Presheaf.germ M.val.presheaf U y' (h.mem_open U.isOpen hy) a :=
  TopCat.Presheaf.germ_stalkSpecializes_apply M.val.presheaf hy h a

lemma modSpec_smul (r : Y.presheaf.stalk y)
    (m : TopCat.Presheaf.stalk (C := Ab.{u}) M.val.presheaf y) :
    modSpec M h (r • m) = (Y.presheaf.stalkSpecializes h).hom r • modSpec M h m := by
  obtain ⟨U, hU, a, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf m
  obtain ⟨V, hV, c, rfl⟩ := TopCat.Presheaf.exists_germ_eq Y.presheaf r
  have hW : y ∈ U ⊓ V := ⟨hU, hV⟩
  have e1 : TopCat.Presheaf.germ M.val.presheaf U y hU a =
      TopCat.Presheaf.germ M.val.presheaf (U ⊓ V) y hW
        (M.presheaf.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op a) :=
    (germ_map_apply M y _ hW a).symm
  have e2 : Y.presheaf.germ V y hV c =
      Y.presheaf.germ (U ⊓ V) y hW (Y.presheaf.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op c) :=
    (TopCat.Presheaf.germ_res_apply Y.presheaf _ y hW c).symm
  rw [e1, e2, ← stalk_germ_smul, modSpec_germ, modSpec_germ,
    TopCat.Presheaf.germ_stalkSpecializes_apply, stalk_germ_smul]

end ModSpec

namespace GG

/-! ## The stalk formula over a ring and its compatibility with specialization -/

section Kaehler

variable {R₀ : Type u} [CommRing R₀] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R₀))

/-- The `R₀`-algebra structure on a stalk of `X`. -/
noncomputable abbrev algSt (x : X) : Algebra R₀ (X.presheaf.stalk x) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R₀)).inv ≫ f.appTop ≫
    X.presheaf.germ ⊤ x trivial).hom.toAlgebra

/-- The stalk formula `(Ω¹_{X/R₀})_x ≃ₗ Ω[𝒪_{X,x}⁄R₀]`. -/
noncomputable def kStalk (x : X) :
    letI := algSt f x
    stalkOmega f x ≃ₗ[X.presheaf.stalk x] Ω[X.presheaf.stalk x⁄R₀] :=
  stalkOmegaEquiv f x

lemma kStalk_germ_dSheaf (x : X) (U : X.Opens) (hx : x ∈ U) (b : Γ(X, U)) :
    letI := algSt f x
    kStalk f x ((TopCat.Presheaf.germ (C := Ab) (X := X.toPresheafedSpace)
        (relOmega f).val.presheaf U x hx).hom (dSheaf f U b)) =
      D R₀ (X.presheaf.stalk x) ((X.presheaf.germ U x hx).hom b) :=
  stalkOmegaEquiv_germ_dSheaf f x U hx b

variable {x x' : X} (h : x' ⤳ x)

/-- The specialization `𝒪_{X,x} → 𝒪_{X,x'}` as an algebra. -/
noncomputable abbrev algSp : Algebra (X.presheaf.stalk x) (X.presheaf.stalk x') :=
  (X.presheaf.stalkSpecializes h).hom.toAlgebra

lemma towerSp :
    letI := algSt f x
    letI := algSt f x'
    letI := algSp h
    IsScalarTower R₀ (X.presheaf.stalk x) (X.presheaf.stalk x') := by
  letI := algSt f x
  letI := algSt f x'
  letI := algSp h
  refine IsScalarTower.of_algebraMap_eq fun r => ?_
  change ((Scheme.ΓSpecIso (CommRingCat.of R₀)).inv ≫ f.appTop ≫
      X.presheaf.germ ⊤ x' trivial).hom r =
    (X.presheaf.stalkSpecializes h).hom (((Scheme.ΓSpecIso (CommRingCat.of R₀)).inv ≫
      f.appTop ≫ X.presheaf.germ ⊤ x trivial).hom r)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  exact (TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf
    (show x ∈ (⊤ : X.Opens) from trivial) h _).symm

/-- The map `Ω[𝒪_{X,x}⁄R₀] → Ω[𝒪_{X,x'}⁄R₀]` along a specialization. -/
noncomputable def kMap :
    letI := algSt f x
    letI := algSt f x'
    letI := algSp h
    Ω[X.presheaf.stalk x⁄R₀] →ₗ[X.presheaf.stalk x] Ω[X.presheaf.stalk x'⁄R₀] :=
  letI := algSt f x
  letI := algSt f x'
  letI := algSp h
  haveI := towerSp f h
  KaehlerDifferential.map R₀ R₀ (X.presheaf.stalk x) (X.presheaf.stalk x')

/-- The stalk formula commutes with specialization. -/
theorem kMap_kStalk (ω : stalkOmega f x) :
    kMap f h (kStalk f x ω) = kStalk f x' (modSpec (relOmega f) h ω) := by
  letI := algSt f x
  letI := algSt f x'
  letI := algSp h
  haveI := towerSp f h
  obtain ⟨w, rfl⟩ := (kStalk f x).symm.surjective ω
  rw [LinearEquiv.apply_symm_apply]
  have hw : w ∈ Submodule.span (X.presheaf.stalk x)
      (Set.range (D R₀ (X.presheaf.stalk x))) := by
    rw [span_range_derivation]; trivial
  induction hw using Submodule.span_induction with
  | mem _ hw' =>
    obtain ⟨t, rfl⟩ := hw'
    obtain ⟨U, hx, b, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf t
    have e1 : (kStalk f x).symm (D R₀ _ ((X.presheaf.germ U x hx).hom b)) =
        (TopCat.Presheaf.germ (C := Ab) (X := X.toPresheafedSpace)
          (relOmega f).val.presheaf U x hx).hom (dSheaf f U b) :=
      (LinearEquiv.symm_apply_eq _).2 (kStalk_germ_dSheaf f x U hx b).symm
    have e2 := modSpec_germ (relOmega f) h U hx (dSheaf f U b)
    have e3 := kStalk_germ_dSheaf f x' U (h.mem_open U.isOpen hx) b
    have e4 : (X.presheaf.stalkSpecializes h).hom ((X.presheaf.germ U x hx).hom b) =
        (X.presheaf.germ U x' (h.mem_open U.isOpen hx)).hom b :=
      TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hx h b
    rw [e1]
    refine Eq.trans ?_ ((congrArg (kStalk f x') e2).trans e3).symm
    change KaehlerDifferential.map R₀ R₀ (X.presheaf.stalk x) (X.presheaf.stalk x')
      (D R₀ _ ((X.presheaf.germ U x hx).hom b)) = _
    rw [KaehlerDifferential.map_D]
    exact congrArg (D R₀ (X.presheaf.stalk x')) e4
  | zero => simp only [map_zero]
  | add a b _ _ ha hb => simp only [map_add, ha, hb]
  | smul a w _ hw =>
    rw [LinearMap.map_smul, LinearEquiv.map_smul, modSpec_smul, LinearEquiv.map_smul, ← hw,
      ← algebraMap_smul (X.presheaf.stalk x') a]
    rfl

end Kaehler

/-! ## The stalks of `e*Ω¹` and the map to the generic fibre -/

section Generic

variable {R₀ : Type u} [CommRing R₀] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R₀))
  (e : Spec (CommRingCat.of R₀) ⟶ X) {η : Spec (CommRingCat.of R₀)} (hη : ∀ s, η ⤳ s)
  (s : Spec (CommRingCat.of R₀))

/-- The specialization `σ : 𝒪_{S,s} → 𝒪_{S,η}`. -/
noncomputable def sig : (Spec (CommRingCat.of R₀)).presheaf.stalk s →+*
    (Spec (CommRingCat.of R₀)).presheaf.stalk η :=
  ((Spec (CommRingCat.of R₀)).presheaf.stalkSpecializes (hη s)).hom

theorem sig_self (t : (Spec (CommRingCat.of R₀)).presheaf.stalk η) : sig hη η t = t := by
  change ((Spec (CommRingCat.of R₀)).presheaf.stalkSpecializes (hη η)).hom t = t
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- `e^♯ : 𝒪_{X,e(s)} → 𝒪_{S,s}`. -/
noncomputable abbrev algBO : Algebra (X.presheaf.stalk (e s))
    ((Spec (CommRingCat.of R₀)).presheaf.stalk s) := (e.stalkMap s).hom.toAlgebra
/-- The specialization `𝒪_{X,e(s)} → 𝒪_{X,e(η)}`. -/
noncomputable abbrev algBXi : Algebra (X.presheaf.stalk (e s)) (X.presheaf.stalk (e η)) :=
  (X.presheaf.stalkSpecializes ((hη s).map e.continuous)).hom.toAlgebra
/-- `σ` as an algebra. -/
noncomputable abbrev algOEta : Algebra ((Spec (CommRingCat.of R₀)).presheaf.stalk s)
    ((Spec (CommRingCat.of R₀)).presheaf.stalk η) := (sig hη s).toAlgebra
/-- `𝒪_{X,e(s)} → 𝒪_{X,e(η)} → 𝒪_{S,η}`. -/
noncomputable abbrev algBEta : Algebra (X.presheaf.stalk (e s))
    ((Spec (CommRingCat.of R₀)).presheaf.stalk η) :=
  ((e.stalkMap η).hom.comp (X.presheaf.stalkSpecializes ((hη s).map e.continuous)).hom).toAlgebra

/-- The stalk `𝒪_{S,s} ⊗_{𝒪_{X,e(s)}} Ω[𝒪_{X,e(s)}⁄R₀]`. -/
noncomputable abbrev StalkT : Type u :=
  letI := algSt f (e s)
  letI := algBO e s
  ((Spec (CommRingCat.of R₀)).presheaf.stalk s) ⊗[X.presheaf.stalk (e s)]
    Ω[X.presheaf.stalk (e s)⁄R₀]

/-- The generic fibre `𝒪_{S,η} ⊗_{𝒪_{X,e(η)}} Ω[𝒪_{X,e(η)}⁄R₀]`. -/
noncomputable abbrev GenT : Type u :=
  letI := algSt f (e η)
  letI := algBO e η
  ((Spec (CommRingCat.of R₀)).presheaf.stalk η) ⊗[X.presheaf.stalk (e η)]
    Ω[X.presheaf.stalk (e η)⁄R₀]

/-- The map from the stalk at `s` to the generic fibre: `r ⊗ ω ↦ σ(r) ⊗ ω|_{e(η)}`. -/
noncomputable def stalkToGeneric : StalkT f e s →+ GenT f e (η := η) :=
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
  (LinearMap.lTensor ((Spec (CommRingCat.of R₀)).presheaf.stalk η)
      (mapBaseChange R₀ (X.presheaf.stalk (e s)) (X.presheaf.stalk (e η)))).toAddMonoidHom.comp
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange
        (X.presheaf.stalk (e s)) (X.presheaf.stalk (e η))
        ((Spec (CommRingCat.of R₀)).presheaf.stalk η)
        ((Spec (CommRingCat.of R₀)).presheaf.stalk η)
        Ω[X.presheaf.stalk (e s)⁄R₀]).symm.toLinearMap.toAddMonoidHom.comp
      (LinearMap.rTensor Ω[X.presheaf.stalk (e s)⁄R₀]
        (IsScalarTower.toAlgHom (X.presheaf.stalk (e s))
          ((Spec (CommRingCat.of R₀)).presheaf.stalk s)
          ((Spec (CommRingCat.of R₀)).presheaf.stalk η)).toLinearMap).toAddMonoidHom)

theorem stalkToGeneric_tmul (r : (Spec (CommRingCat.of R₀)).presheaf.stalk s)
    (ω : letI := algSt f (e s); Ω[X.presheaf.stalk (e s)⁄R₀]) :
    letI := algSt f (e s)
    letI := algSt f (e η)
    letI := algBO e s
    letI := algBO e η
    letI := algBXi e hη s
    stalkToGeneric f e hη s (r ⊗ₜ ω) =
      sig hη s r ⊗ₜ kMap f ((hη s).map e.continuous) ω := by
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
  simp only [stalkToGeneric, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
    LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom',
    LinearEquiv.coe_coe, TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
    LinearMap.lTensor_tmul, mapBaseChange_tmul, one_smul]
  rfl

theorem stalkToGeneric_smul (r' : (Spec (CommRingCat.of R₀)).presheaf.stalk s)
    (x : StalkT f e s) :
    letI := algSt f (e s)
    letI := algBO e s
    letI := algSt f (e η)
    letI := algBO e η
    stalkToGeneric f e hη s (r' • x) = sig hη s r' • stalkToGeneric f e hη s x := by
  letI := algSt f (e s)
  letI := algBO e s
  letI := algSt f (e η)
  letI := algBO e η
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
  | tmul r ω =>
    rw [TensorProduct.smul_tmul', stalkToGeneric_tmul, stalkToGeneric_tmul, smul_eq_mul,
      map_mul, TensorProduct.smul_tmul', smul_eq_mul]

/-- The stalk of `e*Ω¹_{X/R₀}` at `s` is `𝒪_{S,s} ⊗_{𝒪_{X,e(s)}} Ω[𝒪_{X,e(s)}⁄R₀]`. -/
noncomputable def pullStalkEquiv :
    TopCat.Presheaf.stalk (C := Ab.{u}) (pullOmega f e).val.presheaf s ≃ₗ[
      (Spec (CommRingCat.of R₀)).presheaf.stalk s] StalkT f e s :=
  letI := algSt f (e s)
  letI := algBO e s
  (stalkPullbackEquiv e (relOmega f) s).trans
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl _ _) (kStalk f (e s)))

theorem pullStalkEquiv_unitGerm (V : X.Opens) (hV : e s ∈ V) (m : Γ(relOmega f, V)) :
    letI := algSt f (e s)
    letI := algBO e s
    pullStalkEquiv f e s (unitGerm e (relOmega f) s V hV m) =
      (1 : (Spec (CommRingCat.of R₀)).presheaf.stalk s) ⊗ₜ[X.presheaf.stalk (e s)]
        kStalk f (e s) (TopCat.Presheaf.germ (relOmega f).val.presheaf V (e s) hV m) := by
  letI := algSt f (e s)
  letI := algBO e s
  change TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl _ _) (kStalk f (e s))
    (stalkPullbackEquiv e (relOmega f) s (unitGerm e (relOmega f) s V hV m)) = _
  rw [stalkPullbackEquiv_unitGerm]
  rfl

/-- The map from the stalk of `e*Ω¹` at `s` to the generic fibre. -/
noncomputable def phi :
    TopCat.Presheaf.stalk (C := Ab.{u}) (pullOmega f e).val.presheaf s →+ GenT f e (η := η) :=
  (stalkToGeneric f e hη s).comp (pullStalkEquiv f e s).toLinearMap.toAddMonoidHom

theorem phi_apply (m : TopCat.Presheaf.stalk (C := Ab.{u}) (pullOmega f e).val.presheaf s) :
    phi f e hη s m = stalkToGeneric f e hη s (pullStalkEquiv f e s m) := rfl

theorem phi_smul (r : (Spec (CommRingCat.of R₀)).presheaf.stalk s)
    (m : TopCat.Presheaf.stalk (C := Ab.{u}) (pullOmega f e).val.presheaf s) :
    letI := algSt f (e η)
    letI := algBO e η
    phi f e hη s (r • m) = sig hη s r • phi f e hη s m := by
  letI := algSt f (e η)
  letI := algBO e η
  rw [phi_apply, LinearEquiv.map_smul, stalkToGeneric_smul]
  rfl

/-- The value of the map at `s` on the germ of the unit image of a section of `Ω¹`. -/
theorem phi_unitGerm (V : X.Opens) (hV : e s ∈ V) (m : Γ(relOmega f, V)) :
    letI := algSt f (e η)
    letI := algBO e η
    phi f e hη s (unitGerm e (relOmega f) s V hV m) =
      (1 : (Spec (CommRingCat.of R₀)).presheaf.stalk η) ⊗ₜ[X.presheaf.stalk (e η)]
        kStalk f (e η) (TopCat.Presheaf.germ (relOmega f).val.presheaf V (e η)
          (((hη s).map e.continuous).mem_open V.isOpen hV) m) := by
  letI := algSt f (e s)
  letI := algBO e s
  letI := algSt f (e η)
  letI := algBO e η
  refine (congrArg (stalkToGeneric f e hη s) (pullStalkEquiv_unitGerm f e s V hV m)).trans ?_
  rw [stalkToGeneric_tmul, map_one]
  congr 1
  have h1 := kMap_kStalk f ((hη s).map e.continuous)
    (TopCat.Presheaf.germ (relOmega f).val.presheaf V (e s) hV m)
  rw [modSpec_germ] at h1
  exact h1

/-- **The map at `η` composed with the specialization of stalks is the map at `s`.** -/
theorem phi_modSpec (m : TopCat.Presheaf.stalk (C := Ab.{u}) (pullOmega f e).val.presheaf s) :
    phi f e hη η (modSpec (pullOmega f e) (hη s) m) = phi f e hη s m := by
  letI := algSt f (e η)
  letI := algBO e η
  letI : Module ((Spec (CommRingCat.of R₀)).presheaf.stalk s) (GenT f e (η := η)) :=
    Module.compHom _ (sig hη s)
  let L1 : TopCat.Presheaf.stalk (C := Ab.{u}) (pullOmega f e).val.presheaf s →ₗ[
      (Spec (CommRingCat.of R₀)).presheaf.stalk s] GenT f e (η := η) :=
    { toFun := fun m => phi f e hη η (modSpec (pullOmega f e) (hη s) m)
      map_add' := fun a b => by simp only [map_add]
      map_smul' := fun r a => by
        rw [modSpec_smul, phi_smul, sig_self]
        rfl }
  let L2 : TopCat.Presheaf.stalk (C := Ab.{u}) (pullOmega f e).val.presheaf s →ₗ[
      (Spec (CommRingCat.of R₀)).presheaf.stalk s] GenT f e (η := η) :=
    { toFun := fun m => phi f e hη s m
      map_add' := fun a b => map_add _ a b
      map_smul' := fun r a => phi_smul f e hη s r a }
  have key : L1 = L2 := by
    refine stalkPullback_hom_ext (e := e) (M := relOmega f) (s := s) fun V hV m => ?_
    change phi f e hη η (modSpec (pullOmega f e) (hη s) (unitGerm e (relOmega f) s V hV m)) =
      phi f e hη s (unitGerm e (relOmega f) s V hV m)
    have hg : modSpec (pullOmega f e) (hη s) (unitGerm e (relOmega f) s V hV m) =
        unitGerm e (relOmega f) η V ((hη s).mem_open (e ⁻¹ᵁ V).isOpen hV) m :=
      modSpec_germ (pullOmega f e) (hη s) (e ⁻¹ᵁ V) hV _
    exact (congrArg (phi f e hη η) hg).trans
      ((phi_unitGerm f e hη η V _ m).trans (phi_unitGerm f e hη s V hV m).symm)
  exact LinearMap.congr_fun key m

/-- The underlying sheaf of abelian groups of `e*Ω¹`. -/
noncomputable def pullAbSheaf : TopCat.Sheaf Ab.{u} (Spec (CommRingCat.of R₀)) :=
  ⟨(Scheme.Modules.toPresheaf _).obj (pullOmega f e), (pullOmega f e).isSheaf⟩

/-- **The generic germ**: global sections of `e*Ω¹` to the generic fibre. -/
noncomputable def genericGerm : Γ(pullOmega f e, ⊤) →+ GenT f e (η := η) :=
  (phi f e hη η).comp (TopCat.Presheaf.germ (pullOmega f e).val.presheaf ⊤ η trivial).hom

theorem phi_injective (hinj : ∀ s, Function.Injective (stalkToGeneric f e hη s)) :
    Function.Injective (phi f e hη s) :=
  (hinj s).comp (pullStalkEquiv f e s).injective

theorem modSpec_injective (hinj : ∀ s, Function.Injective (stalkToGeneric f e hη s)) :
    Function.Injective (modSpec (pullOmega f e) (hη s)) := fun a b hab => by
  have h := congrArg (phi f e hη η) hab
  rw [phi_modSpec, phi_modSpec] at h
  exact phi_injective f e hη s hinj h

/-- **The generic germ is injective.** -/
theorem genericGerm_injective (hinj : ∀ s, Function.Injective (stalkToGeneric f e hη s)) :
    Function.Injective (genericGerm f e hη) := by
  have hg := germ_injective_of_specializes (pullAbSheaf f e) (U := ⊤) (η := η) trivial
    (fun s _ => hη s) (fun s _ => modSpec_injective f e hη s hinj)
  exact (phi_injective f e hη η hinj).comp hg

/-- **The image of the generic germ is the intersection of the images of the stalks.** -/
theorem range_genericGerm (hinj : ∀ s, Function.Injective (stalkToGeneric f e hη s)) :
    Set.range (genericGerm f e hη) = ⋂ s, Set.range (stalkToGeneric f e hη s) := by
  have hR := range_germ_eq_iInter_specializes (pullAbSheaf f e) (U := ⊤) (η := η) trivial
    (fun s _ => hη s) (fun s _ => modSpec_injective f e hη s hinj)
  ext v
  simp only [Set.mem_iInter, Set.mem_range]
  constructor
  · rintro ⟨σ, rfl⟩ s
    refine ⟨pullStalkEquiv f e s
      (TopCat.Presheaf.germ (pullOmega f e).val.presheaf ⊤ s trivial σ), ?_⟩
    rw [← phi_apply, ← phi_modSpec]
    exact congrArg (phi f e hη η) (modSpec_germ (pullOmega f e) (hη s) ⊤ trivial σ)
  · intro hv
    have hw : ∀ s, ∃ w, phi f e hη s w = v := fun s => by
      obtain ⟨y, hy⟩ := hv s
      exact ⟨(pullStalkEquiv f e s).symm y, by rw [phi_apply, LinearEquiv.apply_symm_apply, hy]⟩
    choose w hw using hw
    have hmem : w η ∈ Set.range
        (ConcreteCategory.hom ((pullAbSheaf f e).presheaf.germ ⊤ η trivial)) := by
      rw [hR]
      refine Set.mem_iInter₂.2 fun s _ => ?_
      refine ⟨w s, phi_injective f e hη η hinj ?_⟩
      change phi f e hη η (modSpec (pullOmega f e) (hη s) (w s)) = _
      rw [phi_modSpec, hw, hw]
    obtain ⟨σ, hσ⟩ := hmem
    refine ⟨σ, ?_⟩
    change phi f e hη η _ = v
    exact (congrArg (phi f e hη η) hσ).trans (hw η)

/-- The germ map at `η` of global sections is linear over `Γ(S, 𝒪_S) → 𝒪_{S,η}`. -/
theorem genericGerm_smul (c : Γ(Spec (CommRingCat.of R₀), ⊤)) (m : Γ(pullOmega f e, ⊤)) :
    letI := algSt f (e η)
    letI := algBO e η
    genericGerm f e hη (c • m) =
      ((Spec (CommRingCat.of R₀)).presheaf.germ ⊤ η trivial).hom c • genericGerm f e hη m := by
  letI := algSt f (e η)
  letI := algBO e η
  change phi f e hη η (TopCat.Presheaf.germ (pullOmega f e).val.presheaf ⊤ η trivial (c • m)) = _
  refine (congrArg (phi f e hη η) (stalk_germ_smul (pullOmega f e) η ⊤ trivial c m)).trans ?_
  rw [phi_smul, sig_self]
  rfl

end Generic

end GG

end ZInQ.HeightModelM5

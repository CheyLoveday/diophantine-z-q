import ZInQKernel.OneProof.H.TailZ24
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.FreeGeneratorPullback

/-! # pic-dict core: the Pic dictionary at `K̄` (glue), Mumford's statements at `A_K̄` (leaves) -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits Opposite MonoidalCategory
open scoped CategoryTheory.MonObj

namespace PicDict

universe u

/-! ## §1. L5: sheafification is the identity at `Spec K̄` -/

/-- A nonempty scheme locally of finite type over an algebraically closed field `k` has a `k`-point
(Mathlib's `pointOfClosedPoint`, Nullstellensatz). -/
theorem exists_section_of_isAlgClosed {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (hf : LocallyOfFiniteType f) (x0 : X) :
    ∃ s : Spec (CommRingCat.of k) ⟶ X, s ≫ f = 𝟙 _ := by
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨x, -, hx⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set X)) ⟨x0, trivial⟩
    isClosed_univ.isLocallyClosed
  exact ⟨pointOfClosedPoint f x hx, pointOfClosedPoint_comp f x hx⟩

/-- **Every fppf covering sieve contains every point with values in an algebraically closed field.** -/
theorem fppf_arrows_of_isAlgClosed {X : Scheme.{u}} {S : Sieve X} (hS : S ∈ Scheme.fppfTopology X)
    {k : Type u} [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ X) : S.arrows s := by
  rw [Precoverage.mem_toGrothendieck_iff] at hS
  induction hS with
  | of X R hR =>
    obtain ⟨I, Y, f, rfl⟩ := R.exists_eq_ofArrows
    rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff] at hR
    obtain ⟨hsurj, hP⟩ := hR
    obtain ⟨i, y, hy⟩ := hsurj (s (IsLocalRing.closedPoint k))
    haveI : Flat (f i) := (hP i).1
    haveI : LocallyOfFinitePresentation (f i) := (hP i).2
    obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f i) (g := s) y
      (IsLocalRing.closedPoint k) hy
    obtain ⟨σ, hσ⟩ := exists_section_of_isAlgClosed (pullback.snd (f i) s) inferInstance z
    refine ⟨Y i, σ ≫ pullback.fst (f i) s, f i, ⟨i⟩, ?_⟩
    rw [Category.assoc, pullback.condition, ← Category.assoc, hσ, Category.id_comp]
  | top X => trivial
  | pullback X S hS Y f ih => exact ih (s ≫ f)
  | transitive X S R hS hR ihS ihR =>
    have h1 := ihR (ihS s) (𝟙 _)
    simpa using h1

/-- `Spec K̄` in `Over (Spec K)`: every fppf covering sieve is the maximal sieve. -/
theorem over_fppf_id_mem {K : Type} [Field K] {S : Sieve (T09Pic.ptK K)}
    (hS : S ∈ (Scheme.fppfTopology.over (Spec (CommRingCat.of K))) (T09Pic.ptK K)) :
    S.arrows (𝟙 _) := by
  rw [GrothendieckTopology.mem_over_iff] at hS
  have h := fppf_arrows_of_isAlgClosed hS (k := AlgebraicClosure K) (𝟙 _)
  replace h := (Sieve.overEquiv_iff S _).1 h
  have h2 := S.downward_closed h
    (Over.homMk (𝟙 (T09Pic.ptK K).left) (by simp) :
      T09Pic.ptK K ⟶ Over.mk (𝟙 _ ≫ (T09Pic.ptK K).hom))
  convert h2 using 1
  ext
  exact (Category.id_comp _).symm

/-- **L5 is a theorem** (`T09Pic.PicPointsAlgClosed`; Kleiman 9.2.5 at `T = Spec K̄`). -/
theorem picPointsAlgClosed : T09Pic.PicPointsAlgClosed := by
  intro K _ A
  constructor
  · intro c c' h
    haveI : Presheaf.IsLocallyInjective (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      (toPicardFunctor A.X.hom) := Presheaf.isLocallyInjective_toSheafify' _ (picardPresheaf A.X.hom)
    have hm := Presheaf.equalizerSieve_mem (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      (toPicardFunctor A.X.hom) c c' h
    have := over_fppf_id_mem hm
    simpa [Presheaf.equalizerSieve] using this
  · intro s
    haveI : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      (toPicardFunctor A.X.hom) := Presheaf.isLocallySurjective_toSheafify' _ (picardPresheaf A.X.hom)
    have hm := Presheaf.imageSieve_mem (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      (toPicardFunctor A.X.hom) s
    obtain ⟨t, ht⟩ := over_fppf_id_mem hm
    exact ⟨t, by simpa using ht⟩

open T09Pic PkgI3 PkgI3.AbVar HDec.WeilPairing

variable {K : Type} [Field K]

/-- `A_K̄ = A ×_K K̄` as a scheme (the scheme of `weilScalar`). -/
abbrev AK (A : AbVar K) : Scheme.{0} := pullback A.X.hom (ptK K).hom

/-! ## §2. The dictionary `B(K̄) → Pic(A_K̄)`, `y ↦ M_y = picClass y` (glue, proved) -/

section Dictionary

variable {A : AbVar K} {P : Over (Spec (CommRingCat.of K))}
  (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) {B : AbVar K} (j : B.X ⟶ P)

theorem toPicardFunctor_picClass (y : B.Pt (AlgebraicClosure K)) :
    (toPicardFunctor A.X.hom).app (op (ptK K)) (picClass rep j y) = rep.homEquiv (y ≫ j) := by
  have h : ∃ c, (toPicardFunctor A.X.hom).app (op (ptK K)) c = rep.homEquiv (y ≫ j) :=
    (picPointsAlgClosed K A).2 _
  have e : picClass rep j y = h.choose := by
    unfold picClass
    exact dif_pos h
  rw [e]
  exact h.choose_spec

theorem picClass_eq_iff (y : B.Pt (AlgebraicClosure K)) (c : (AK A).Pic) :
    picClass rep j y = c ↔
      (toPicardFunctor A.X.hom).app (op (ptK K)) c = rep.homEquiv (y ≫ j) :=
  ⟨fun h => h ▸ toPicardFunctor_picClass rep j y,
   fun h => (picPointsAlgClosed K A).1 ((toPicardFunctor_picClass rep j y).trans h.symm)⟩

theorem picClass_mul {j : B.X ⟶ P} (hj : IsPicZero rep B j) (y y' : B.Pt (AlgebraicClosure K)) :
    picClass rep j (y * y') = picClass rep j y * picClass rep j y' := by
  letI := picardFunctorCommGrpObj A.X.hom rep
  haveI : IsMonHom j := hj.2.2
  rw [picClass_eq_iff, ← Equiv.symm_apply_eq, homEquiv_symm_toPicardFunctor_mul,
    toPicardFunctor_picClass, toPicardFunctor_picClass, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply, MonObj.mul_comp]

theorem picClass_injective {j : B.X ⟶ P} (hj : IsPicZero rep B j) :
    Function.Injective (picClass rep j) := by
  intro y y' h
  have h1 := (toPicardFunctor_picClass rep j y).symm.trans
    (h ▸ toPicardFunctor_picClass rep j y')
  have h2 : y ≫ j = y' ≫ j := rep.homEquiv.injective h1
  haveI : IsOpenImmersion j.left := hj.1
  apply Over.OverMorphism.ext
  exact (cancel_mono j.left).1 (by rw [← Over.comp_left, h2, Over.comp_left])

/-- `y ↦ M_y` as a group homomorphism `B(K̄) → Pic(A_K̄)`. -/
def picHom {j : B.X ⟶ P} (hj : IsPicZero rep B j) : B.Pt (AlgebraicClosure K) →* (AK A).Pic :=
  MonoidHom.mk' (picClass rep j) (picClass_mul rep hj)

@[simp] lemma picHom_apply {j : B.X ⟶ P} (hj : IsPicZero rep B j) (y) :
    picHom rep hj y = picClass rep j y := rfl

/-- The Galois action on `B(K̄)` corresponds to pull-back along `1 × Spec σ` on `A_K̄`. -/
theorem picClass_gal (σ : Gal K) (y : B.Pt (AlgebraicClosure K)) :
    picClass rep j (galHom σ ≫ y) =
      Scheme.Pic.map (JacobianChallenge.baseChangeMap A.X.hom (galHom σ)) (picClass rep j y) := by
  rw [picClass_eq_iff]
  have hn := (toPicardFunctor A.X.hom).naturality_apply (galHom σ).op (picClass rep j y)
  refine hn.trans ?_
  rw [toPicardFunctor_picClass, ← rep.homEquiv_comp, Category.assoc]

/-- The dual morphism `f^∨` acts on `K̄`-points of `Pic⁰` by pull-back along `f × 1`. -/
theorem picClass_dual (f : A.X ⟶ A.X) (fv : B.X ⟶ B.X) (hfv : fv ≫ j = j ≫ dualP rep f)
    (y : B.Pt (AlgebraicClosure K)) :
    picClass rep j (y ≫ fv) = Scheme.Pic.map (famMap f (ptK K)) (picClass rep j y) := by
  rw [picClass_eq_iff, Category.assoc, hfv, ← Category.assoc, comp_dualP, Equiv.apply_symm_apply,
    ← toPicardFunctor_picClass]
  have := congrArg (fun τ => τ.app (op (ptK K)) (picClass rep j y))
    (toPicardFunctor_comp_dualSheafMap f)
  exact this.symm

end Dictionary

/-! ## §3. Translations, `φ_L` on points -/

/-- `t_x` on the scheme `A_K̄`. -/
abbrev trl {A : AbVar K} (x : A.Pt (AlgebraicClosure K)) : AK A ⟶ AK A := (transl x).left

/-- `n_A` on the scheme `A_K̄`. -/
abbrev mlN (A : AbVar K) (n : ℕ) : AK A ⟶ AK A := (mulN A n).left

/-- `L_K̄ = p₁^*L`. -/
def bcPic (A : AbVar K) (L : A.X.left.Pic) : (AK A).Pic :=
  Scheme.Pic.map (pullback.fst A.X.hom (ptK K).hom) L

/-- Mumford's `φ_L(x) = t_x^*L ⊗ L⁻¹` (§8). -/
def phiPt {A : AbVar K} (c : (AK A).Pic) (x : A.Pt (AlgebraicClosure K)) : (AK A).Pic :=
  Scheme.Pic.map (trl x) c * c⁻¹

/-- Mumford's `Pic⁰(A_K̄)`: classes invariant under every translation `t_x`, `x ∈ A(K̄)` (§8). -/
def IsTranslInv {A : AbVar K} (c : (AK A).Pic) : Prop :=
  ∀ x : A.Pt (AlgebraicClosure K), Scheme.Pic.map (trl x) c = c

/-- Mumford's `Â_n = Pic⁰(A_K̄)[n]`. -/
def IsDualTors {A : AbVar K} (n : ℕ) (c : (AK A).Pic) : Prop := IsTranslInv c ∧ c ^ n = 1

theorem transl_comp_transl {A : AbVar K} (z x : A.Pt (AlgebraicClosure K)) :
    transl z ≫ transl x = transl (z * x) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [transl, Category.assoc, CartesianMonoidalCategory.lift_fst]
    rw [← CategoryTheory.Hom.mul_def, ← CategoryTheory.Hom.mul_def, ← CategoryTheory.Hom.mul_def,
      MonObj.comp_mul, CartesianMonoidalCategory.lift_fst, CartesianMonoidalCategory.lift_snd_assoc,
      mul_assoc, ← MonObj.comp_mul]
  · simp [transl]

/-- **Glue (proved): `φ_L(x)` lies in Mumford's `Pic⁰`**, from the theorem of the square. -/
theorem phiPt_translInv {A : AbVar K}
    (hsq : ∀ (c : (AK A).Pic) (x y : A.Pt (AlgebraicClosure K)),
      Scheme.Pic.map (trl (x * y)) c * c =
        Scheme.Pic.map (trl x) c * Scheme.Pic.map (trl y) c)
    (c : (AK A).Pic) (x : A.Pt (AlgebraicClosure K)) : IsTranslInv (phiPt c x) := by
  intro z
  have h1 : Scheme.Pic.map (trl z) (Scheme.Pic.map (trl x) c) =
      Scheme.Pic.map (trl (z * x)) c := by
    rw [← Scheme.Pic.map_comp, ← Over.comp_left, transl_comp_transl]
  have h2 := hsq c z x
  simp only [phiPt, ← Scheme.Pic.mapHom_apply, map_mul, map_inv] at h2 ⊢
  simp only [Scheme.Pic.mapHom_apply] at h2 ⊢
  rw [h1]
  have : Scheme.Pic.map (trl (z * x)) c =
      Scheme.Pic.map (trl z) c * Scheme.Pic.map (trl x) c * c⁻¹ := by
    rw [← h2]; group
  rw [this, mul_comm (_ * _ * _) _]
  simp [mul_assoc]

/-- `A_K̄ → A × A`, `(a, s) ↦ (a, x(s))` is `(A ◁ x).left`. -/
lemma baseChangeMap_pt {A : AbVar K} (x : A.Pt (AlgebraicClosure K)) :
    JacobianChallenge.baseChangeMap A.X.hom x = (A.X ◁ x).left := by
  apply pullback.hom_ext <;> simp [JacobianChallenge.baseChangeMap]

/-- **`Λ(L)` restricted along `x`** is `φ_{L_K̄}(x)` (glue, proved). -/
theorem map_mumfordBundle_pt {A : AbVar K} (L : A.X.left.Pic) (x : A.Pt (AlgebraicClosure K)) :
    Scheme.Pic.map (JacobianChallenge.baseChangeMap A.X.hom x) (mumfordBundle A L) =
      phiPt (bcPic A L) x := by
  have hμ : JacobianChallenge.baseChangeMap A.X.hom x ≫ (μ[A.X]).left =
      (transl x).left ≫ pullback.fst A.X.hom (ptK K).hom := by
    rw [baseChangeMap_pt, ← Over.comp_left]
    have : (transl x).left ≫ pullback.fst A.X.hom (ptK K).hom =
        (transl x ≫ CartesianMonoidalCategory.fst A.X (ptK K)).left := by simp
    rw [this]
    congr 1
    simp only [transl, CartesianMonoidalCategory.lift_fst]
    congr 1
  have hfst : JacobianChallenge.baseChangeMap A.X.hom x ≫ pullback.fst A.X.hom A.X.hom =
      pullback.fst A.X.hom (ptK K).hom := pullback.lift_fst _ _ _
  have hsnd : JacobianChallenge.baseChangeMap A.X.hom x ≫ pullback.snd A.X.hom A.X.hom =
      pullback.snd _ _ ≫ x.left := pullback.lift_snd _ _ _
  have hS : Scheme.Pic.map x.left L = 1 :=
    Subsingleton.elim (α := (Spec (CommRingCat.of (AlgebraicClosure K))).Pic) _ _
  rw [mumfordBundle, ← Scheme.Pic.mapHom_apply]
  simp only [map_mul, map_inv, Scheme.Pic.mapHom_apply, ← Scheme.Pic.map_comp, hμ, hsnd, hfst]
  rw [Scheme.Pic.map_comp (pullback.snd _ _) x.left, hS, Scheme.Pic.map_one, Scheme.Pic.map_comp]
  simp [phiPt, bcPic]

/-- **`M_{λ_L(x)} = φ_{L_K̄}(x)`** (glue, proved). -/
theorem picClass_phiL {A : AbVar K} {P : Over (Spec (CommRingCat.of K))}
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) {B : AbVar K} {j : B.X ⟶ P}
    (L : A.X.left.Pic) (lam : A.X ⟶ B.X) (hlam : lam ≫ j = phiL rep L)
    (x : A.Pt (AlgebraicClosure K)) :
    picClass rep j (x ≫ lam) = phiPt (bcPic A L) x := by
  rw [picClass_eq_iff, Category.assoc, hlam, phiL, comp_classify, Equiv.apply_symm_apply,
    map_mumfordBundle_pt]

/-- **Lifting `K̄`-points along a surjective morphism locally of finite type** (Nullstellensatz). -/
theorem exists_lift_pt {A B : AbVar K} (lam : A.X ⟶ B.X) [LocallyOfFiniteType lam.left]
    (hs : Surjective lam.left) (y : B.Pt (AlgebraicClosure K)) :
    ∃ x : A.Pt (AlgebraicClosure K), x ≫ lam = y := by
  obtain ⟨a, ha⟩ := hs.surj (y.left (IsLocalRing.closedPoint (AlgebraicClosure K)))
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := lam.left) (g := y.left) a
    (IsLocalRing.closedPoint (AlgebraicClosure K)) ha
  have hlft : LocallyOfFiniteType (pullback.snd lam.left y.left) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) (IsPullback.of_hasPullback _ _)
      inferInstance
  obtain ⟨σ, hσ⟩ := exists_section_of_isAlgClosed (pullback.snd lam.left y.left) hlft z
  have hc : σ ≫ pullback.fst lam.left y.left ≫ lam.left = y.left := by
    rw [pullback.condition]
    have := congrArg (· ≫ y.left) hσ
    exact (Category.assoc _ _ _).symm.trans (this.trans (Category.id_comp _))
  refine ⟨Over.homMk (σ ≫ pullback.fst lam.left y.left) ?_, ?_⟩
  · change (σ ≫ pullback.fst lam.left y.left) ≫ A.X.hom = (ptK K).hom
    rw [← Over.w lam, Category.assoc, reassoc_of% hc]
    exact Over.w y
  · apply Over.OverMorphism.ext
    show (σ ≫ pullback.fst lam.left y.left) ≫ lam.left = y.left
    rw [Category.assoc]
    exact hc

/-! ## §4. Mumford's `ē_n` by its formula, on any class -/

/-- The module of a class. -/
abbrev mod {A : AbVar K} (c : (AK A).Pic) : (AK A).Modules :=
  (fromSkeleton (AK A).Modules).obj c.val

/-- Trivializations `ψ : 𝒪 ≅ n_A^*M` of `n_A^*M` on `A_K̄`. -/
abbrev Triv (A : AbVar K) (n : ℕ) (c : (AK A).Pic) :=
  Scheme.Modules.unit (AK A) ≅ (Scheme.Modules.pullback (mulN A n).left).obj (mod c)

/-- **Mumford's formula** `ē_n(x, M) = t_x^*ψ ∘ ψ⁻¹ ∈ Γ(A_K̄, 𝒪)` for `x ∈ A[n](K̄)` and a trivialization
`ψ : 𝒪 ≅ n_A^*M` (Mumford §20; the right side of `weilScalar_spec`). -/
def weilFormula {A : AbVar K} {n : ℕ} (x : tors A n) (c : (AK A).Pic) (ψ : Triv A n c) :
    Γ(AK A, ⊤) :=
  Scheme.Modules.unitHomAddEquiv (Scheme.Modules.unit _)
    ((Scheme.Modules.pullbackObjUnitIso (transl (Additive.toMul (x : P A))).left).inv ≫
      (Scheme.Modules.pullback (transl (Additive.toMul (x : P A))).left).map ψ.hom ≫
      (Scheme.Modules.pullbackComp _ _).hom.app _ ≫
      (Scheme.Modules.pullbackCongr (transl_left_comp_mulN_left x)).hom.app _ ≫ ψ.inv)

end PicDict

section TransportSection

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite

namespace PicDict.Transport

open Scheme.Modules

universe u

variable {X Y Z : Scheme.{u}}

/-- `𝒪 → (f ≫ h)_* 𝒪` is the composite of `𝒪 → h_* 𝒪 → h_* f_* 𝒪`. -/
lemma unitToPushforward_comp (f : X ⟶ Y) (h : Y ⟶ Z) :
    SheafOfModules.unitToPushforwardObjUnit (f ≫ h).toRingCatSheafHom =
      SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom ≫
        (pushforward h).map (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
          (pushforwardComp f h).hom.app (unit X) := by
  ext U x
  rfl

/-- **`pullbackObjUnitIso` is compatible with `pullbackComp`.** -/
lemma pullbackObjUnitIso_comp (f : X ⟶ Y) (h : Y ⟶ Z) :
    (pullbackComp f h).inv.app _ ≫ (Scheme.Modules.pullback f).map (pullbackObjUnitIso h).hom ≫
      (pullbackObjUnitIso f).hom = (pullbackObjUnitIso (f ≫ h)).hom := by
  haveI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (pullbackPushforwardAdjunction f).isRightAdjoint
  haveI : (SheafOfModules.pushforward h.toRingCatSheafHom).IsRightAdjoint :=
    (pullbackPushforwardAdjunction h).isRightAdjoint
  haveI : (SheafOfModules.pushforward (f ≫ h).toRingCatSheafHom).IsRightAdjoint :=
    (pullbackPushforwardAdjunction (f ≫ h)).isRightAdjoint
  apply ((pullbackPushforwardAdjunction (f ≫ h)).homEquiv _ _).injective
  have hR : (pullbackPushforwardAdjunction (f ≫ h)).homEquiv _ _ (pullbackObjUnitIso (f ≫ h)).hom =
      SheafOfModules.unitToPushforwardObjUnit (f ≫ h).toRingCatSheafHom :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  have hf : (pullbackPushforwardAdjunction f).homEquiv _ _ (pullbackObjUnitIso f).hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  have hh : (pullbackPushforwardAdjunction h).homEquiv _ _ (pullbackObjUnitIso h).hom =
      SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  rw [hR, unitToPushforward_comp]
  set adj₁ := (pullbackPushforwardAdjunction h).comp (pullbackPushforwardAdjunction f)
  set adj₂ := pullbackPushforwardAdjunction (f ≫ h)
  set Yf := (Scheme.Modules.pullback f).map (pullbackObjUnitIso h).hom ≫ (pullbackObjUnitIso f).hom
  have hc := conjugateEquiv_pullbackComp_inv f h
  have hu := unit_conjugateEquiv adj₁ adj₂ (pullbackComp f h).inv (unit Z)
  rw [hc] at hu
  have key : adj₂.homEquiv _ _ ((pullbackComp f h).inv.app _ ≫ Yf) =
      adj₁.homEquiv _ _ Yf ≫ (pushforwardComp f h).hom.app (unit X) := by
    rw [adj₂.homEquiv_unit, adj₁.homEquiv_unit, Functor.map_comp, ← Category.assoc, ← hu,
      Category.assoc, Category.assoc]
    congr 1
  rw [key, ← Category.assoc]
  refine congrArg (fun φ => φ ≫ (pushforwardComp f h).hom.app (unit X)) ?_
  rw [Adjunction.comp_homEquiv]
  show (pullbackPushforwardAdjunction h).homEquiv _ _ ((pullbackPushforwardAdjunction f).homEquiv _ _
    ((Scheme.Modules.pullback f).map (pullbackObjUnitIso h).hom ≫ (pullbackObjUnitIso f).hom)) = _
  rw [Adjunction.homEquiv_naturality_left, hf, Adjunction.homEquiv_naturality_right, hh]

end PicDict.Transport

namespace PicDict.Transport

open Scheme.Modules

universe v

variable {X Y Z W : Scheme.{v}}

lemma pullbackCongr_hom_app {f f' : X ⟶ Y} (e : f = f') (M : Y.Modules) :
    (pullbackCongr e).hom.app M = eqToHom (by rw [e]) := by
  subst e; rfl

/-- naturality of `pullbackComp` in the first variable -/
lemma eqToHom_comp_pullbackComp {f f' : X ⟶ Y} (e : f = f') (h : Y ⟶ Z) (M : Z.Modules)
    (p : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback h).obj M) =
      (Scheme.Modules.pullback f').obj ((Scheme.Modules.pullback h).obj M)) :
    eqToHom p ≫ (pullbackComp f' h).hom.app M =
      (pullbackComp f h).hom.app M ≫ eqToHom (by rw [e]) := by
  subst e; simp

/-- naturality of `pullbackComp` in the second variable -/
lemma map_eqToHom_comp_pullbackComp (f : X ⟶ Y) {h h' : Y ⟶ Z} (e : h = h') (M : Z.Modules)
    (p : (Scheme.Modules.pullback h).obj M = (Scheme.Modules.pullback h').obj M) :
    (Scheme.Modules.pullback f).map (eqToHom p) ≫ (pullbackComp f h').hom.app M =
      (pullbackComp f h).hom.app M ≫ eqToHom (by rw [e]) := by
  subst e; simp

/-- associativity of `pullbackComp`, on objects -/
lemma pullbackComp_assoc_app (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (M : W.Modules) :
    (Scheme.Modules.pullback f).map ((pullbackComp g h).hom.app M) ≫
        (pullbackComp f (g ≫ h)).hom.app M =
      (pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj M) ≫
        (pullbackComp (f ≫ g) h).hom.app M ≫ eqToHom (by rw [Category.assoc]) := by
  have H := congrArg (fun τ => τ.app M) (pseudofunctor_associativity f g h)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Category.id_comp, eqToHom_app] at H
  have H1 := (Iso.inv_comp_eq ((pullbackComp f (g ≫ h)).app M)).mp H
  have H2 := (Iso.inv_comp_eq ((Scheme.Modules.pullback f).mapIso ((pullbackComp g h).app M))).mp H1
  simp only [Functor.mapIso_hom, Iso.app_hom] at H2
  rw [← Category.assoc ((pullbackComp f g).hom.app _), H2]
  simp

lemma pullbackCongr_inv_app {f f' : X ⟶ Y} (e : f = f') (M : Y.Modules) :
    (pullbackCongr e).inv.app M = eqToHom (by rw [e]) := by
  subst e; rfl

lemma pullbackComp_assoc_inv₁ (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (M : W.Modules) :
    (Scheme.Modules.pullback f).map ((pullbackComp g h).inv.app M) ≫
        (pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj M) ≫
          (pullbackComp (f ≫ g) h).hom.app M =
      (pullbackComp f (g ≫ h)).hom.app M ≫ eqToHom (by rw [Category.assoc]) := by
  rw [← cancel_epi ((Scheme.Modules.pullback f).map ((pullbackComp g h).hom.app M)),
    ← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    reassoc_of% (pullbackComp_assoc_app f g h M)]
  simp

lemma pullbackComp_assoc_inv₂ (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (M : W.Modules) :
    (pullbackComp f g).inv.app ((Scheme.Modules.pullback h).obj M) ≫
        (Scheme.Modules.pullback f).map ((pullbackComp g h).hom.app M) ≫
          (pullbackComp f (g ≫ h)).hom.app M =
      (pullbackComp (f ≫ g) h).hom.app M ≫ eqToHom (by rw [Category.assoc]) := by
  rw [pullbackComp_assoc_app, Iso.inv_hom_id_app_assoc]

/-- `g^* m^* M ≅ m^* g^* M` for `g ≫ m = m ≫ g`. -/
def Qiso (g m : X ⟶ X) (hb : g ≫ m = m ≫ g) (M : X.Modules) :
    (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback m).obj M) ≅
      (Scheme.Modules.pullback m).obj ((Scheme.Modules.pullback g).obj M) :=
  (pullbackComp g m).app M ≪≫ (pullbackCongr hb).app M ≪≫ ((pullbackComp m g).app M).symm

/-- `t'^* g^* ≅ g^* t^*` for `t' ≫ g = g ≫ t`. -/
def Niso (t' g t : X ⟶ X) (ha : t' ≫ g = g ≫ t) :
    Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback t' ≅
      Scheme.Modules.pullback t ⋙ Scheme.Modules.pullback g :=
  pullbackComp t' g ≪≫ pullbackCongr ha ≪≫ (pullbackComp g t).symm

/-- **Coherence (II).** -/
lemma coherence_II (t' g m t : X ⟶ X) (ha : t' ≫ g = g ≫ t) (hb : g ≫ m = m ≫ g)
    (h : t ≫ m = m) (h' : t' ≫ m = m) (M : X.Modules) :
    (Niso t' g t ha).inv.app ((Scheme.Modules.pullback m).obj M) ≫
        (Scheme.Modules.pullback t').map (Qiso g m hb M).hom ≫
          (pullbackComp t' m).hom.app ((Scheme.Modules.pullback g).obj M) ≫
            (pullbackCongr h').hom.app ((Scheme.Modules.pullback g).obj M) ≫ (Qiso g m hb M).inv =
      (Scheme.Modules.pullback g).map
        ((pullbackComp t m).hom.app M ≫ (pullbackCongr h).hom.app M) := by
  rw [← cancel_mono ((pullbackComp g m).hom.app M)]
  simp only [Niso, Qiso, Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom, Iso.app_hom,
    Iso.app_inv, NatTrans.comp_app, Functor.map_comp, Category.assoc, Iso.inv_hom_id_app,
    Category.comp_id, pullbackCongr_hom_app, pullbackCongr_inv_app]
  -- RHS
  rw [map_eqToHom_comp_pullbackComp g h M, reassoc_of% (pullbackComp_assoc_app g t m M)]
  -- LHS
  rw [reassoc_of% (eqToHom_comp_pullbackComp h' g M)]
  rw [reassoc_of% (pullbackComp_assoc_inv₁ t' m g M)]
  rw [reassoc_of% (map_eqToHom_comp_pullbackComp t' hb M)]
  rw [reassoc_of% (pullbackComp_assoc_inv₂ t' g m M)]
  rw [reassoc_of% (eqToHom_comp_pullbackComp ha.symm m M)]
  simp

/-- `pullbackObjUnitIso` with its type stated through `Scheme.Modules.unit`. -/
def pOU (f : X ⟶ Y) : (Scheme.Modules.pullback f).obj (unit Y) ≅ unit X := pullbackObjUnitIso f

lemma pOU_comp (f : X ⟶ Y) (h : Y ⟶ Z) :
    (pullbackComp f h).inv.app (unit Z) ≫ (Scheme.Modules.pullback f).map (pOU h).hom ≫
      (pOU f).hom = (pOU (f ≫ h)).hom :=
  pullbackObjUnitIso_comp f h

lemma pOU_conj (h : Y ⟶ X) (f : unit X ⟶ unit X) :
    ((pOU h).inv ≫ (Scheme.Modules.pullback h).map f ≫ (pOU h).hom).app ⊤ (1 : Γ(Y, ⊤)) =
      h.appTop (f.app ⊤ (1 : Γ(X, ⊤))) :=
  pullbackObjUnitIso_conj_app_top h f

lemma pOU_inv_comp (f : X ⟶ Y) (h : Y ⟶ Z) :
    (pOU (f ≫ h)).inv = (pOU f).inv ≫
      (Scheme.Modules.pullback f).map (pOU h).inv ≫ (pullbackComp f h).hom.app (unit _) := by
  refine Iso.inv_ext ?_
  rw [← pOU_comp f h]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
  exact Iso.inv_hom_id_app _ _

lemma pOU_inv_congr {f f' : X ⟶ Y} (e : f = f') :
    (pOU f).inv ≫ (pullbackCongr e).hom.app (unit _) = (pOU f').inv := by
  subst e; simp [pullbackCongr]

set_option maxHeartbeats 1600000 in
/-- **Coherence (I).** -/
lemma coherence_I (t' g t : X ⟶ X) (ha : t' ≫ g = g ≫ t) :
    (pOU t').inv ≫ (Scheme.Modules.pullback t').map (pOU g).inv ≫
        (Niso t' g t ha).hom.app (unit _) =
      (pOU g).inv ≫ (Scheme.Modules.pullback g).map (pOU t).inv := by
  simp only [Niso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [← reassoc_of% (pOU_inv_comp t' g), reassoc_of% (pOU_inv_congr ha), pOU_inv_comp g t]
  simp

/-- The generic Weil formula. -/
def wf (t m : X ⟶ X) (h : t ≫ m = m) (M : X.Modules)
    (ψ : unit X ≅ (Scheme.Modules.pullback m).obj M) : Γ(X, ⊤) :=
  unitHomAddEquiv (unit X) ((pOU t).inv ≫ (Scheme.Modules.pullback t).map ψ.hom ≫
    (pullbackComp t m).hom.app M ≫ (pullbackCongr h).hom.app M ≫ ψ.inv)

/-- The transported trivialization. -/
def transTriv (g m : X ⟶ X) (hb : g ≫ m = m ≫ g) (M : X.Modules)
    (ψ : unit X ≅ (Scheme.Modules.pullback m).obj M) :
    unit X ≅ (Scheme.Modules.pullback m).obj ((Scheme.Modules.pullback g).obj M) :=
  (pOU g).symm ≪≫ (Scheme.Modules.pullback g).mapIso ψ ≪≫ Qiso g m hb M

/-- **Transport of Mumford's formula along `g`.** -/
theorem wf_transport (t' g m t : X ⟶ X) (ha : t' ≫ g = g ≫ t) (hb : g ≫ m = m ≫ g)
    (h : t ≫ m = m) (h' : t' ≫ m = m) (M : X.Modules)
    (ψ : unit X ≅ (Scheme.Modules.pullback m).obj M) :
    wf t' m h' ((Scheme.Modules.pullback g).obj M) (transTriv g m hb M ψ) =
      g.appTop (wf t m h M ψ) := by
  simp only [wf, unitHomAddEquiv_apply]
  rw [← pOU_conj g]
  congr 2
  have nat := (Niso t' g t ha).hom.naturality ψ.hom
  have e1 : (Scheme.Modules.pullback t').map ((Scheme.Modules.pullback g).map ψ.hom) =
      (Niso t' g t ha).hom.app _ ≫ (Scheme.Modules.pullback g).map ((Scheme.Modules.pullback t).map ψ.hom) ≫
        (Niso t' g t ha).inv.app _ := by
    simp only [Functor.comp_map] at nat
    rw [← Category.assoc, ← nat]; simp
  simp only [transTriv, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, Functor.map_comp, Category.assoc]
  rw [e1]
  simp only [Category.assoc]
  rw [reassoc_of% (coherence_I t' g t ha)]
  have h2 := coherence_II t' g m t ha hb h h' M
  simp only [Functor.map_comp] at h2
  rw [reassoc_of% h2]

/-- Invariance under isomorphisms of the module. -/
theorem wf_iso (t m : X ⟶ X) (h : t ≫ m = m) {M₁ M₂ : X.Modules} (e : M₁ ≅ M₂)
    (ψ : unit X ≅ (Scheme.Modules.pullback m).obj M₁) :
    wf t m h M₂ (ψ ≪≫ (Scheme.Modules.pullback m).mapIso e) = wf t m h M₁ ψ := by
  have n1 := (pullbackComp t m).hom.naturality e.hom
  have n2 := (pullbackCongr h).hom.naturality e.hom
  simp only [Functor.comp_map] at n1
  simp only [wf, Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    Functor.map_comp, Category.assoc]
  rw [reassoc_of% n1, reassoc_of% n2]
  simp

end PicDict.Transport

end TransportSection

namespace PicDict

open T09Pic PkgI3 PkgI3.AbVar HDec.WeilPairing CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

variable {K : Type} [Field K]

/-- `1 × Spec σ` on `A_K̄`. -/
abbrev gal (A : AbVar K) (σ : Gal K) : AK A ⟶ AK A :=
  JacobianChallenge.baseChangeMap A.X.hom (galHom σ)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma gal_eq (A : AbVar K) (σ : Gal K) : gal A σ = (A.X ◁ galHom σ).left := by
  apply Limits.pullback.hom_ext <;> simp [JacobianChallenge.baseChangeMap]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma transl_gal (A : AbVar K) (σ : Gal K) (x : A.Pt (AlgebraicClosure K)) :
    transl (galHom σ ≫ x) ≫ (A.X ◁ galHom σ) = (A.X ◁ galHom σ) ≫ transl x := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [transl, CartesianMonoidalCategory.comp_lift_assoc]
  · simp [transl]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma gal_transl (A : AbVar K) (σ : Gal K) (x : A.Pt (AlgebraicClosure K)) :
    trl (galHom σ ≫ x) ≫ gal A σ = gal A σ ≫ trl x := by
  rw [gal_eq, ← Over.comp_left, ← Over.comp_left, transl_gal]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma gal_mulN (A : AbVar K) (σ : Gal K) (n : ℕ) : gal A σ ≫ mlN A n = mlN A n ≫ gal A σ := by
  rw [gal_eq, ← Over.comp_left, ← Over.comp_left]
  congr 1
  unfold mulN
  exact whisker_exchange _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma gal_constK (A : AbVar K) (σ : Gal K) (u : AlgebraicClosure K) :
    (gal A σ).appTop (constK A u) = constK A (σ u) := by
  have hs : gal A σ ≫ Limits.pullback.snd A.X.hom (ptK K).hom =
      Limits.pullback.snd A.X.hom (ptK K).hom ≫ (galHom σ).left := Limits.pullback.lift_snd _ _ _
  simp only [constK, RingHom.comp_apply]
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hs, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply]
  congr 1
  have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (σ : AlgebraicClosure K →+* AlgebraicClosure K))
  exact (congrArg (fun φ => φ.hom u) this).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma weilFormula_eq_wf {A : AbVar K} {n : ℕ} (x : tors A n) (c : (AK A).Pic) (ψ : Triv A n c) :
    weilFormula x c ψ = Transport.wf (trl (Additive.toMul (x : P A))) (mlN A n)
      (transl_left_comp_mulN_left x) (mod c) ψ := rfl

/-- **GLUE, proved form**: transport along `σ ∈ G_K`. -/
def WeilFormulaGaloisEx : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (n : ℕ) (σ : Gal K) (x : tors A n) (c c' : (AK A).Pic),
      c' = Scheme.Pic.map (gal A σ) c →
      ∀ (ψ : Triv A n c) (u : AlgebraicClosure K),
        weilFormula x c ψ = constK A u →
          ∃ ψ' : Triv A n c', weilFormula (galTors A n σ x) c' ψ' = constK A (σ u)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem weilFormulaGaloisEx : WeilFormulaGaloisEx := by
  intro K _ A n σ x c c' hc ψ u hu
  subst hc
  let e : (Scheme.Modules.pullback (gal A σ)).obj (mod c) ≅ mod (Scheme.Pic.map (gal A σ) c) :=
    (Scheme.Pic.mkIso _).symm
  refine ⟨Transport.transTriv (gal A σ) (mlN A n) (gal_mulN A σ n) (mod c) ψ ≪≫
    (Scheme.Modules.pullback (mlN A n)).mapIso e, ?_⟩
  have ha : (transl (Additive.toMul ((galTors A n σ x : tors A n) : P A))).left ≫ gal A σ =
      gal A σ ≫ trl (Additive.toMul (x : P A)) := gal_transl A σ _
  have h1 := Transport.wf_iso (transl (Additive.toMul ((galTors A n σ x : tors A n) : P A))).left (mlN A n)
    (transl_left_comp_mulN_left (galTors A n σ x)) e
    (Transport.transTriv (gal A σ) (mlN A n) (gal_mulN A σ n) (mod c) ψ)
  have h2 := Transport.wf_transport (transl (Additive.toMul ((galTors A n σ x : tors A n) : P A))).left
    (gal A σ) (mlN A n) (trl (Additive.toMul (x : P A))) ha (gal_mulN A σ n)
    (transl_left_comp_mulN_left x) (transl_left_comp_mulN_left (galTors A n σ x)) (mod c) ψ
  have h3 : weilFormula x c ψ = Transport.wf (trl (Additive.toMul (x : P A))) (mlN A n)
    (transl_left_comp_mulN_left x) (mod c) ψ := rfl
  have h4 := weilFormula_eq_wf (galTors A n σ x) (Scheme.Pic.map (gal A σ) c)
      (Transport.transTriv (gal A σ) (mlN A n) (gal_mulN A σ n) (mod c) ψ ≪≫
        (Scheme.Modules.pullback (mlN A n)).mapIso e)
  rw [h4, h1, h2, ← h3, hu]
  exact gal_constK A σ u


/-! ## §5. Leaves: Mumford's printed statements for the abelian variety `X = A_K̄` over `k = K̄` -/

/-- **LEAF (theorem of the square).** For an abelian variety `X` over an algebraically closed field `k`,
`L ∈ Pic(X)` and `x, y ∈ X(k)`: `t_{x+y}^*L ⊗ L ≅ t_x^*L ⊗ t_y^*L`. Mumford, *Abelian varieties*, §6,
Cor. 4 (UNVERIFIED numbering). Instance `X = A_K̄`, `X(K̄) = A(K̄)`. -/
def MumfordSquare : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (c : (AK A).Pic) (x y : A.Pt (AlgebraicClosure K)),
    Scheme.Pic.map (trl (x * y)) c * c =
      Scheme.Pic.map (trl x) c * Scheme.Pic.map (trl y) c

/-- **LEAF (`n_X^*L ≅ Lⁿ` on `Pic⁰`).** For `L ∈ Pic⁰(X)` (`t_x^*L ≅ L` for all `x ∈ X(k)`), `n_X^*L ≅ Lⁿ`.
Mumford §8 (iv) (UNVERIFIED numbering). Instance `X = A_K̄`. -/
def MumfordMulNPicZero : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (c : (AK A).Pic), IsTranslInv c →
    ∀ n : ℕ, Scheme.Pic.map (mlN A n) c = c ^ n

/-- **LEAF (`φ_L` maps onto `Pic⁰`).** For `L` ample and `M ∈ Pic⁰(X)` there is `x ∈ X(k)` with
`M ≅ t_x^*L ⊗ L⁻¹`. Mumford §8, Thm 1 (UNVERIFIED numbering). Instance `X = A_K̄`. -/
def MumfordPhiSurjective : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (c₀ : (AK A).Pic), IsAmple (AK A) c₀ →
    ∀ c : (AK A).Pic, IsTranslInv c → ∃ x : A.Pt (AlgebraicClosure K), c = phiPt c₀ x

/-- **LEAF (ampleness and field extension).** If `L` is ample on `X` over `K` then `L_{K'}` is ample on
`X_{K'}` for a field extension `K'/K` (EGA II 4.6.13 (iii); Stacks, Tag 0D2M? UNVERIFIED numbering).
Instance `K' = K̄`. -/
def AmpleBaseChangeAlgClosure : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : A.X.left.Pic), IsAmple A.X.left L →
    IsAmple (AK A) (bcPic A L)

/-- **LEAF (`ē_n` well defined, `μ_n`-valued, bilinear).** For `x, x' ∈ X_n` and `M, M' ∈ X̂_n`, Mumford's
`ē_n(x, M) = t_x^*ψ ∘ ψ⁻¹` does not depend on the trivialization `ψ : 𝒪 ≅ n^*M`, is a constant in `μ_n(k)`,
and is bimultiplicative. Mumford §20 (definition of `ē_n` and its bilinearity; UNVERIFIED numbering).
Instance `X = A_K̄`, stated for `n ≥ 1` prime to the characteristic. -/
def MumfordWeilPairing : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (n : ℕ), 0 < n → (n : K) ≠ 0 →
    ∀ (x x' : tors A n) (c c' : (AK A).Pic), IsDualTors n c → IsDualTors n c' →
      (∀ ψ ψ' : Triv A n c, weilFormula x c ψ = weilFormula x c ψ') ∧
      (∀ ψ : Triv A n c, ∃ u : (AlgebraicClosure K)ˣ, u ^ n = 1 ∧
        constK A (u : AlgebraicClosure K) = weilFormula x c ψ) ∧
      (∀ ψ : Triv A n c, weilFormula (x + x') c ψ = weilFormula x c ψ * weilFormula x' c ψ) ∧
      (∀ (ψ : Triv A n c) (ψ' : Triv A n c') (ψ'' : Triv A n (c * c')),
        weilFormula x (c * c') ψ'' = weilFormula x c ψ * weilFormula x c' ψ')

/-- **LEAF (`ē_n` nondegenerate).** For `n` prime to the characteristic, `ē_n : X_n × X̂_n → μ_n` has trivial
kernels. Mumford §20 (UNVERIFIED numbering). Instance `X = A_K̄`. -/
def MumfordWeilNondeg : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (n : ℕ), 0 < n → (n : K) ≠ 0 →
    (∀ x : tors A n, (∀ c : (AK A).Pic, IsDualTors n c → ∀ ψ : Triv A n c, weilFormula x c ψ = 1) →
      x = 0) ∧
    (∀ c : (AK A).Pic, IsDualTors n c → (∀ (x : tors A n) (ψ : Triv A n c), weilFormula x c ψ = 1) →
      c = 1)

/-- **LEAF (`ē_{mn}(x, M) = ē_n(mx, M)` for `M ∈ X̂_n`).** Mumford §20 (UNVERIFIED numbering). Instance
`X = A_K̄`. -/
def MumfordWeilCompat : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (m n : ℕ), 0 < m → 0 < n → ((m * n : ℕ) : K) ≠ 0 →
    ∀ (x : tors A (m * n)) (c : (AK A).Pic), IsDualTors n c →
      ∀ (ψ : Triv A (m * n) c) (ψ' : Triv A n c),
        weilFormula x c ψ = weilFormula (torsSmul A m n x) c ψ'

/-- **LEAF (`ē_n(x, f^*M) = ē_n(f x, M)`).** For a homomorphism `f : X → X`, Mumford §20 (5) (stated there for
isogenies) and Milne 1986, Lemma 16.2(c) (every homomorphism); UNVERIFIED numbering. Instance `X = A_K̄`,
`f = g_K̄` for `g ∈ End_K(A)`. -/
def MumfordWeilDual : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (n : ℕ), 0 < n → (n : K) ≠ 0 →
    ∀ (f : End A) (x : tors A n) (c : (AK A).Pic), IsDualTors n c →
      ∀ (ψ : Triv A n (Scheme.Pic.map (famMap f.hom (ptK K)) c)) (ψ' : Triv A n c),
        weilFormula x (Scheme.Pic.map (famMap f.hom (ptK K)) c) ψ = weilFormula (torsMap f n x) c ψ'

/-- **LEAF (`e^L_n(x, x) = 1`).** For `L ∈ Pic(X)` and `x ∈ X_n`, `ē_n(x, φ_L(x)) = 1`. Mumford §23
(`e^L_n(x, y) = ē_n(x, φ_L(y))` and `e^L_n(x, x) = 1`; UNVERIFIED numbering). Instance `X = A_K̄`. -/
def MumfordWeilAlt : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (n : ℕ), 0 < n → (n : K) ≠ 0 →
    ∀ (c₀ : (AK A).Pic) (x : tors A n) (ψ : Triv A n (phiPt c₀ (Additive.toMul (x : P A)))),
      weilFormula x (phiPt c₀ (Additive.toMul (x : P A))) ψ = 1

/-! ## §6. Assembly: `WeilPairingMumford` from the leaves (glue, proved) -/

theorem constK_injective (A : AbVar K) : Function.Injective (constK A) := by
  have : Nonempty (𝟙_ (Over (Spec (CommRingCat.of K)))).left :=
    inferInstanceAs (Nonempty (Spec (CommRingCat.of K)))
  have : Nonempty A.X.left := ⟨η[A.X].left (Nonempty.some inferInstance)⟩
  have : Nonempty (ptK K).left :=
    inferInstanceAs (Nonempty (Spec (CommRingCat.of (AlgebraicClosure K))))
  have : Subsingleton (Spec (CommRingCat.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have hX : Nonempty ↥(pullback A.X.hom (ptK K).hom : Scheme.{0}) := inferInstance
  have : Nonempty (⊤ : (pullback A.X.hom (ptK K).hom : Scheme.{0}).Opens) :=
    ⟨⟨hX.some, trivial⟩⟩
  exact (constK A).injective

theorem nonempty_triv {A : AbVar K} {n : ℕ} {c : (AK A).Pic}
    (h : Scheme.Pic.map (mlN A n) c = 1) : Nonempty (Triv A n c) := by
  obtain ⟨e⟩ := Scheme.Pic.eq_iff_nonempty_iso.1 h
  exact ⟨(Scheme.Pic.oneIso).symm ≪≫ e.symm ≪≫ Scheme.Pic.mkIso _⟩

theorem weilFormula_congr {A : AbVar K} {n : ℕ} (x : tors A n) {c c' : (AK A).Pic} (h : c = c')
    (ψ : Triv A n c) : weilFormula x c' (h ▸ ψ) = weilFormula x c ψ := by
  subst h; rfl

/-- The pairing with values `u x y`, as a `Pairing`. -/
def mkPairing {A B : AbVar K} {n : ℕ} (u : tors A n → tors B n → (AlgebraicClosure K)ˣ)
    (hu : ∀ x y, u x y ^ n = 1) (hx : ∀ x x' y, u (x + x') y = u x y * u x' y)
    (hy : ∀ x y y', u x (y + y') = u x y * u x y') : Pairing A B n :=
  AddMonoidHom.mk' (fun x => AddMonoidHom.mk'
      (fun y => Additive.ofMul (⟨u x y, (mem_rootsOfUnity n _).2 (hu x y)⟩ :
        rootsOfUnity n (AlgebraicClosure K)))
      (fun y y' => by
        apply Additive.toMul.injective
        apply Subtype.ext
        simp [hy]))
    (fun x x' => by
      refine AddMonoidHom.ext fun y => ?_
      apply Additive.toMul.injective
      apply Subtype.ext
      simp [hx])

@[simp] lemma mkPairing_val {A B : AbVar K} {n : ℕ} (u : tors A n → tors B n → (AlgebraicClosure K)ˣ)
    (hu hx hy) (x y) : (mkPairing (n := n) u hu hx hy x y).val = u x y := rfl

/-- **Main result (`WeilPairingMumford`).** From Mumford's statements at `A_K̄` (theorem of the square,
§8 (iv), §8 Thm 1, §20, §23), ampleness under field extension and the row `PhiAmpleIsogeny`; L5
(`picPointsAlgClosed`), the dictionary and the Galois transport (`weilFormulaGaloisEx`) are proved. -/
theorem weilPairingMumford_of_printed (hsq : MumfordSquare) (h8iv : MumfordMulNPicZero)
    (h8 : MumfordPhiSurjective) (hamp : AmpleBaseChangeAlgClosure) (h20a : MumfordWeilPairing)
    (h20b : MumfordWeilNondeg) (h20c : MumfordWeilCompat) (h20d : MumfordWeilDual)
    (h23 : MumfordWeilAlt) (h3 : PhiAmpleIsogeny) :
    WeilPairingMumford := by
  classical
  intro K _ A P rep B j hj
  obtain ⟨L, hL⟩ := exists_isVeryAmple A
  have hLa := veryAmpleIsAmple K A L hL
  obtain ⟨lam, hlam⟩ := exists_hom_comp_eq_phiL rep hj L
  obtain ⟨hfin, hsurj⟩ := h3 K A P rep B j hj L hLa lam.hom hlam
  -- `B(K̄) ⊆ Pic⁰(A_K̄)`
  have hsub : ∀ y, IsTranslInv (picClass rep j y) := fun y => by
    obtain ⟨x, rfl⟩ := exists_lift_pt lam.hom hsurj y
    rw [picClass_phiL rep L lam.hom hlam x]
    exact phiPt_translInv (hsq K A) _ x
  -- `Pic⁰(A_K̄) ⊆ B(K̄)`
  have hsup : ∀ c, IsTranslInv c → ∃ y, picClass rep j y = c := fun c hc => by
    obtain ⟨x, rfl⟩ := h8 K A _ (hamp K A L hLa) c hc
    exact ⟨x ≫ lam.hom, picClass_phiL rep L lam.hom hlam x⟩
  have hone : picClass rep j 1 = 1 := map_one (picHom rep hj)
  have htors : ∀ (n : ℕ) (y : tors B n),
      IsDualTors n (picClass rep j (Additive.toMul (y : HDec.WeilPairing.P B))) := fun n y => by
    refine ⟨hsub _, ?_⟩
    rw [← picHom_apply rep hj, ← map_pow, ← toMul_nsmul, nsmul_tors y]
    exact hone
  have htriv : ∀ (n : ℕ) (y : tors B n),
      Nonempty (Triv A n (picClass rep j (Additive.toMul (y : HDec.WeilPairing.P B)))) :=
    fun n y => nonempty_triv (by rw [h8iv K A _ (hsub _) n, (htors n y).2])
  have hspec : ∀ (n : ℕ) (x : tors A n) (y : tors B n),
      weilScalar rep j n (Additive.toMul (x : HDec.WeilPairing.P A))
          (Additive.toMul (y : HDec.WeilPairing.P B)) =
        weilFormula x (picClass rep j (Additive.toMul (y : HDec.WeilPairing.P B))) (htriv n y).some := by
    intro n x y
    unfold weilScalar
    rw [dite_eq_left (transl_left_comp_mulN_left x)]
    exact dite_eq_left (htriv n y)
  have hval : ∀ (n : ℕ) (hn : 0 < n) (hnK : (n : K) ≠ 0) (x : tors A n) (y : tors B n),
      ∃ u : (AlgebraicClosure K)ˣ, u ^ n = 1 ∧ constK A (u : AlgebraicClosure K) =
        weilScalar rep j n (Additive.toMul (x : HDec.WeilPairing.P A))
          (Additive.toMul (y : HDec.WeilPairing.P B)) := by
    intro n hn hnK x y
    rw [hspec]
    exact (h20a K A n hn hnK x x _ _ (htors n y) (htors n y)).2.1 _
  choose u hu1 hu2 using hval
  -- the values are pinned by `weilScalar`
  have hpin : ∀ (n : ℕ) (hn : 0 < n) (hnK : (n : K) ≠ 0) (x : tors A n) (y : tors B n)
      (v : (AlgebraicClosure K)ˣ), constK A (v : AlgebraicClosure K) =
        weilScalar rep j n (Additive.toMul (x : HDec.WeilPairing.P A))
          (Additive.toMul (y : HDec.WeilPairing.P B)) → u n hn hnK x y = v := by
    intro n hn hnK x y v hv
    exact Units.ext (constK_injective A ((hu2 n hn hnK x y).trans hv.symm))
  have hux : ∀ (n : ℕ) (hn : 0 < n) (hnK : (n : K) ≠ 0) (x x' : tors A n) (y : tors B n),
      u n hn hnK (x + x') y = u n hn hnK x y * u n hn hnK x' y := by
    intro n hn hnK x x' y
    apply hpin
    rw [Units.val_mul, map_mul, hu2, hu2, hspec, hspec, hspec]
    exact ((h20a K A n hn hnK x x' _ _ (htors n y) (htors n y)).2.2.1 _).symm
  have huy : ∀ (n : ℕ) (hn : 0 < n) (hnK : (n : K) ≠ 0) (x : tors A n) (y y' : tors B n),
      u n hn hnK x (y + y') = u n hn hnK x y * u n hn hnK x y' := by
    intro n hn hnK x y y'
    apply hpin
    rw [Units.val_mul, map_mul, hu2, hu2, hspec, hspec, hspec]
    have hc : picClass rep j (Additive.toMul ((y + y' : tors B n) : HDec.WeilPairing.P B)) =
        picClass rep j (Additive.toMul (y : HDec.WeilPairing.P B)) *
          picClass rep j (Additive.toMul (y' : HDec.WeilPairing.P B)) :=
      picClass_mul rep hj _ _
    rw [← weilFormula_congr x hc]
    exact ((h20a K A n hn hnK x x _ _ (htors n y) (htors n y')).2.2.2 _ _ _).symm
  let e : ∀ n : ℕ, Pairing A B n := fun n =>
    if h : 0 < n ∧ (n : K) ≠ 0 then
      mkPairing (u n h.1 h.2) (hu1 n h.1 h.2) (hux n h.1 h.2) (huy n h.1 h.2)
    else 0
  have he : ∀ (n : ℕ) (hn : 0 < n) (hnK : (n : K) ≠ 0) (x : tors A n) (y : tors B n),
      (e n x y).val = u n hn hnK x y := by
    intro n hn hnK x y
    simp only [e, dif_pos (And.intro hn hnK), mkPairing_val]
  have he0 : ∀ (n : ℕ) (hn : 0 < n) (hnK : (n : K) ≠ 0) (x : tors A n) (y : tors B n),
      e n x y = 0 ↔ weilFormula x (picClass rep j (Additive.toMul (y : HDec.WeilPairing.P B)))
        (htriv n y).some = 1 := by
    intro n hn hnK x y
    constructor
    · intro h
      have h1 := he n hn hnK x y
      rw [h, Mu.val_zero] at h1
      rw [← hspec, ← hu2 n hn hnK x y, ← h1]
      simp
    · intro h
      apply Mu.val_injective
      rw [he n hn hnK x y, Mu.val_zero]
      apply hpin
      rw [hspec, h]
      simp
  -- independence of the trivialization
  have hind : ∀ (n : ℕ) (hn : 0 < n) (hnK : (n : K) ≠ 0) (x : tors A n) (c : (AK A).Pic),
      IsDualTors n c → ∀ ψ ψ' : Triv A n c, weilFormula x c ψ = weilFormula x c ψ' :=
    fun n hn hnK x c hc ψ ψ' => (h20a K A n hn hnK x x c c hc hc).1 ψ ψ'
  refine ⟨e, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- perfect
    intro n hn hnK
    refine ⟨fun x hx => ?_, fun y hy => ?_⟩
    · apply (h20b K A n hn hnK).1 x
      intro c hc ψ
      obtain ⟨y0, hy0⟩ := hsup c hc.1
      have hy0t : Additive.ofMul y0 ∈ tors B n := by
        rw [mem_tors]
        apply Additive.toMul.injective
        apply picClass_injective rep hj
        rw [toMul_nsmul, toMul_ofMul, toMul_zero, ← picHom_apply rep hj, map_pow, picHom_apply, hy0,
          hc.2, hone]
      have h1 := (he0 n hn hnK x ⟨_, hy0t⟩).1 (hx _)
      have hy0' : picClass rep j (Additive.toMul ((⟨_, hy0t⟩ : tors B n) : HDec.WeilPairing.P B)) =
          c := hy0
      rw [← weilFormula_congr x hy0'] at h1
      rw [hind n hn hnK x c hc ψ _]
      exact h1
    · have hc := (h20b K A n hn hnK).2 _ (htors n y) (fun x ψ => by
        rw [hind n hn hnK x _ (htors n y) ψ (htriv n y).some]
        exact (he0 n hn hnK x y).1 (hy x))
      exact Subtype.ext (Additive.toMul.injective (picClass_injective rep hj (hc.trans hone.symm)))
  · -- Galois
    intro n hn hnK σ x y
    apply Mu.val_injective
    apply Units.ext
    rw [he n hn hnK, galMu_val, he n hn hnK]
    apply constK_injective A
    rw [hu2, hspec]
    have hg : picClass rep j (Additive.toMul ((galTors B n σ y : tors B n) : HDec.WeilPairing.P B)) =
        Scheme.Pic.map (JacobianChallenge.baseChangeMap A.X.hom (galHom σ))
          (picClass rep j (Additive.toMul (y : HDec.WeilPairing.P B))) :=
      picClass_gal rep j σ _
    obtain ⟨ψ', hψ'⟩ := weilFormulaGaloisEx K A n σ x _ _ hg (htriv n y).some _
      ((hspec n x y).symm.trans (hu2 n hn hnK x y).symm)
    rw [hind n hn hnK _ _ (htors n (galTors B n σ y)) _ ψ']
    exact hψ'
  · -- compatibility
    intro m n hm hn hmnK x y
    have hnK : (n : K) ≠ 0 := by
      intro h; apply hmnK; rw [Nat.cast_mul, h, mul_zero]
    have hmn : 0 < m * n := Nat.mul_pos hm hn
    rw [he (m * n) hmn hmnK, he n hn hnK]
    apply hpin
    rw [hu2, hspec, hspec]
    exact (h20c K A m n hm hn hmnK x _ (htors n y) _ _).symm
  · -- adjoint
    intro f fv hfv n hn hnK x y
    apply Mu.val_injective
    rw [he n hn hnK, he n hn hnK]
    apply hpin
    rw [hu2, hspec, hspec]
    have hd : picClass rep j (Additive.toMul ((torsMap fv n y : tors B n) : HDec.WeilPairing.P B)) =
        Scheme.Pic.map (famMap f.hom (ptK K))
          (picClass rep j (Additive.toMul (y : HDec.WeilPairing.P B))) :=
      picClass_dual rep j f.hom fv.hom hfv _
    rw [← weilFormula_congr x hd]
    exact (h20d K A n hn hnK f x _ (htors n y) _ _).symm
  · -- `e_n(x, λ_L x) = 1`
    intro L' hL' lam' hlam' n hn hnK x
    rw [he0 n hn hnK]
    have hp : picClass rep j (Additive.toMul ((torsMap lam' n x : tors B n) : HDec.WeilPairing.P B)) =
        phiPt (bcPic A L') (Additive.toMul (x : HDec.WeilPairing.P A)) :=
      picClass_phiL rep L' lam'.hom hlam' _
    rw [← weilFormula_congr x hp]
    exact h23 K A n hn hnK _ x _
  · -- the pin
    intro n hn hnK x y
    rw [he n hn hnK]
    exact hu2 n hn hnK x y

/-! ## §7. `PhiAmpleIsogeny`: surjectivity from `K̄`-points (glue, proved), finiteness (named glue) -/

/-- Every closed point of a scheme locally of finite type over `K` is the image of a `K̄`-point. -/
theorem exists_pt_of_isClosed {B : AbVar K} (b : B.X.left) (hb : IsClosed {b}) :
    ∃ y : B.Pt (AlgebraicClosure K), y.left (IsLocalRing.closedPoint (AlgebraicClosure K)) = b := by
  haveI : IsFinite (B.X.left.fromSpecResidueField b ≫ B.X.hom) := by
    rw [isClosed_singleton_iff_isClosedImmersion] at hb
    rw [isFinite_iff_locallyOfFiniteType_of_jacobsonSpace]
    infer_instance
  let φ := Spec.preimage (B.X.left.fromSpecResidueField b ≫ B.X.hom)
  have hφ : Spec.map φ = B.X.left.fromSpecResidueField b ≫ B.X.hom := Spec.map_preimage _
  have hfin : φ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hφ]; infer_instance
  letI : Algebra K (B.X.left.residueField b) := φ.hom.toAlgebra
  haveI : Module.Finite K (B.X.left.residueField b) := hfin
  haveI : Algebra.IsIntegral K (B.X.left.residueField b) := Algebra.IsIntegral.of_finite _ _
  let ψ : B.X.left.residueField b →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  refine ⟨Over.homMk (Spec.map (CommRingCat.ofHom (ψ : B.X.left.residueField b →+* AlgebraicClosure K)) ≫
    B.X.left.fromSpecResidueField b) ?_, ?_⟩
  · change (_ ≫ _) ≫ B.X.hom = Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
    rw [Category.assoc, ← hφ, ← Spec.map_comp]
    congr 1
    ext a
    exact ψ.commutes a
  · show (Spec.map _ ≫ B.X.left.fromSpecResidueField b) _ = b
    exact Scheme.fromSpecResidueField_apply b _

/-- **Surjectivity from surjectivity on `K̄`-points** (glue, proved): the image of `lam` is closed (`lam`
is proper) and contains every closed point of the Jacobson scheme `B`. -/
theorem surjective_of_forall_pt {A B : AbVar K} (lam : A.X ⟶ B.X)
    (h : ∀ y : B.Pt (AlgebraicClosure K), ∃ x : A.Pt (AlgebraicClosure K), x ≫ lam = y) :
    Surjective lam.left := by
  haveI : IsProper (lam.left ≫ B.X.hom) := by rw [Over.w lam]; infer_instance
  haveI : IsProper lam.left := IsProper.of_comp lam.left B.X.hom
  have hcl : IsClosed (Set.range lam.left) := lam.left.isClosedMap.isClosed_range
  haveI : JacobsonSpace B.X.left := LocallyOfFiniteType.jacobsonSpace B.X.hom
  have hcp : closedPoints B.X.left ⊆ Set.range lam.left := by
    intro b hb
    obtain ⟨y, rfl⟩ := exists_pt_of_isClosed b hb
    obtain ⟨x, rfl⟩ := h y
    exact ⟨x.left (IsLocalRing.closedPoint _), rfl⟩
  constructor
  intro b
  have : b ∈ closure (closedPoints B.X.left) := by rw [closure_closedPoints]; trivial
  exact (closure_minimal hcp hcl) this

/-- **LEAF (`K(L)` is finite for ample `L`).** For `L` ample on an abelian variety `X` over an algebraically
closed field, `K(L) = {x ∈ X(k) : t_x^*L ≅ L}` is finite. Mumford §6, Application 1 (printed for `L = 𝒪(D)`,
`D` effective; for general ample `L`, `L^m` is effective and `K(L) ⊆ K(L^m)`); UNVERIFIED numbering. Instance
`X = A_K̄`. -/
def MumfordKLFinite : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (c₀ : (AK A).Pic), IsAmple (AK A) c₀ →
    {x : A.Pt (AlgebraicClosure K) | phiPt c₀ x = 1}.Finite

/-- **LEAF? (`K̄`-points of `Pic⁰_{A/K}` are translation-invariant).** For `y ∈ B(K̄)`, `B` the identity
component of `Pic_{A/K}`, the class `M_y` lies in Mumford's `Pic⁰(A_K̄)`. Composite: Kleiman, *The Picard
scheme*, Prop. 9.5.10 (the `K̄`-points of `Pic⁰` are the classes algebraically equivalent to `0`) with Mumford
§8 (classes algebraically equivalent to `0` are translation-invariant); UNVERIFIED numbering. -/
def PicZeroPtsTranslInv : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (P : Over (Spec (CommRingCat.of K)))
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (B : AbVar K) (j : B.X ⟶ P),
    IsPicZero rep B j → ∀ y : B.Pt (AlgebraicClosure K), IsTranslInv (picClass rep j y)

/-- **GLUE (finite kernel on `K̄`-points ⇒ finite).** A homomorphism of abelian varieties over `K` whose kernel
has finitely many `K̄`-points is a finite morphism (proper and quasi-finite). -/
def FiniteOfFiniteKerPts : Prop :=
  ∀ (K : Type) [Field K] (A B : AbVar K) (f : Hom A B),
    {x : A.Pt (AlgebraicClosure K) | x ≫ f.hom = 1}.Finite → IsFinite f.hom.left

/-- **`PhiAmpleIsogeny` from the leaves** (glue, proved): the kernel of `λ_L` on `K̄`-points is `K(L_K̄)`
(dictionary), and `λ_L` is onto on `K̄`-points (Mumford §8 Thm 1 and `PicZeroPtsTranslInv`). -/
theorem phiAmpleIsogeny_of_printed (hKL : MumfordKLFinite) (h8 : MumfordPhiSurjective)
    (hamp : AmpleBaseChangeAlgClosure) (hsub : PicZeroPtsTranslInv) (hfin : FiniteOfFiniteKerPts) :
    PhiAmpleIsogeny := by
  intro K _ A P rep B j hj L hL lam hlam
  obtain ⟨lam', hlam'⟩ := exists_hom_comp_eq_phiL rep hj L
  have hjm : Mono j := by
    haveI : IsOpenImmersion j.left := hj.1
    exact (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono j.left))
  have he : lam = lam'.hom := by rw [← cancel_mono j, hlam, hlam']
  subst he
  have hone : picClass rep j 1 = 1 := map_one (picHom rep hj)
  refine ⟨hfin K A B lam' ((hKL K A _ (hamp K A L hL)).subset fun x hx => ?_), ?_⟩
  · change x ≫ lam'.hom = 1 at hx
    change phiPt (bcPic A L) x = 1
    rw [← picClass_phiL rep L lam'.hom hlam x, hx, hone]
  · apply surjective_of_forall_pt
    intro y
    obtain ⟨x, hx⟩ := h8 K A _ (hamp K A L hL) _ (hsub K A P rep B j hj y)
    exact ⟨x, picClass_injective rep hj (by rw [picClass_phiL rep L lam'.hom hlam x, hx])⟩

end PicDict

import ZInQKernel.Contrib.OneProof.CMHeight62Full.GroupCurveNotP1

/-!
# A translation fixes no degree-one place (the translation hypothesis of the group-curve lemma)

Let `kb` be a field and `X` a group scheme over `Spec kb` (a group object of `Over (Spec kb)`)
which is universally closed and separated over `kb` (for instance proper). For a point `y` of `X`,
the residue field `κ(y)` is a `kb`-algebra. Places of `κ(y)/kb` are valuation subrings, as in
`GroupCurveNotP1`.

* `TranslationNoFixedPlace.exists_fixed_point_of_comap_eq`: if a `kb`-automorphism `f` of `X`
  fixes `y` and the induced automorphism of `κ(y)` maps a degree-one place `Q` onto itself, then
  `f` fixes a `kb`-point of `X` (the centre of `Q`, from the valuative criteria of universal
  closedness and separatedness).
* `noFixedDegreeOnePlace_of_noFixedPoint`: hence an automorphism without `kb`-fixed points induces
  an automorphism of `κ(y)` that fixes no degree-one place.
* `translation_noFixedDegreeOnePlace`: the translation `x ↦ a · x` by a `kb`-point `a ≠ 1` has no
  `kb`-fixed point, so it fixes no degree-one place of `κ(y)` whenever it fixes `y`.
* `exists_noFixedPlace_baseChange`: the same for the base change of a proper group scheme `G/S`
  along any `Spec kb → S` (e.g. a geometric special fibre of a proper smooth group model).
* `not_hasSimplePoleOnlyAt_of_translation`: combined with `not_hasSimplePoleOnlyAt_of_baseChange`.
* `TranslationNoFixedPlace.translationInput_of_component`: over an algebraically closed `kb`, if
  `X` is proper and `y` is the non-closed generic point of an irreducible component through the
  unit, some `kb`-point `a ≠ 1` has a translation fixing `y` (a closed point `a ≠ 1` of the
  component lying on no other component, from the Jacobson property; it is a `kb`-point by the
  Nullstellensatz; the translation by `a` maps the component onto a component through `a`).
* `exists_noFixedPlace_of_component`, `exists_noFixedPlace_baseChange_of_component`: the
  automorphism of `κ(y)` for such `y`, also on a fibre of a proper group scheme.
* `not_hasSimplePoleOnlyAt_of_component`: the group-curve lemma for such `y`; that `y` is not
  closed follows from the degree-one place (a closed point has residue field `kb`).

Only Mathlib and `GroupCurveNotP1` are used.
-/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CMHeight62Full

namespace TranslationNoFixedPlace

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

universe u

variable {kb : Type u} [Field kb]

section Residue

variable (X : Over (Spec (CommRingCat.of kb)))

/-- The structure map `kb → κ(y)` of a point of a `kb`-scheme. -/
def residueAlgHom (y : X.left) : kb →+* X.left.residueField y :=
  ((Scheme.ΓSpecIso (CommRingCat.of kb)).inv ≫ X.hom.appTop ≫ X.left.Γevaluation y).hom

instance residueAlgebra (y : X.left) : Algebra kb (X.left.residueField y) :=
  (residueAlgHom X y).toAlgebra

theorem algebraMap_residue_eq (y : X.left) :
    algebraMap kb (X.left.residueField y) = residueAlgHom X y := rfl

theorem spec_fromSpecResidueField_eq {k : Type u} [Field k] (x : Spec (CommRingCat.of k)) :
    Spec.map (Scheme.Spec.residueFieldIsoOfField x).inv =
      (Spec (CommRingCat.of k)).fromSpecResidueField x := by
  rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField, ← Spec.map_comp]
  congr 1
  rw [Scheme.Spec.residueFieldIsoOfField_eq]
  ext a
  simp [Ideal.algEquivResidueFieldOfField_apply]

theorem fromSpecResidueField_hom (y : X.left) :
    X.left.fromSpecResidueField y ≫ X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap kb (X.left.residueField y))) := by
  rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← spec_fromSpecResidueField_eq,
    ← Spec.map_comp, Scheme.Hom.residueFieldIsoOfField_inv_residueFieldMap]
  rfl

end Residue

section Translate

variable (X : Over (Spec (CommRingCat.of kb))) [GrpObj X]

/-- Translation `x ↦ a · x` by a `kb`-point `a`. -/
def translate (a : 𝟙_ (Over (Spec (CommRingCat.of kb))) ⟶ X) : X ⟶ X :=
  lift (toUnit X ≫ a) (𝟙 X) ≫ MonObj.mul

variable {X}

theorem comp_translate {T : Over (Spec (CommRingCat.of kb))}
    (a : 𝟙_ (Over (Spec (CommRingCat.of kb))) ⟶ X) (p : T ⟶ X) :
    p ≫ translate X a = (toUnit T ≫ a) * p := by
  rw [translate, Hom.mul_def, ← Category.assoc, comp_lift, ← Category.assoc,
    toUnit_unique (p ≫ toUnit X) (toUnit T), Category.comp_id]

theorem translate_eq_mul (a : 𝟙_ (Over (Spec (CommRingCat.of kb))) ⟶ X) :
    translate X a = (toUnit X ≫ a) * 𝟙 X := by
  simpa using comp_translate a (𝟙 X)

theorem translate_comp_translate (a b : 𝟙_ (Over (Spec (CommRingCat.of kb))) ⟶ X) :
    translate X a ≫ translate X b = translate X (b * a) := by
  rw [comp_translate, translate_eq_mul, translate_eq_mul, ← _root_.mul_assoc, MonObj.comp_mul]

theorem translate_one : translate X (1 : 𝟙_ (Over (Spec (CommRingCat.of kb))) ⟶ X) = 𝟙 X := by
  rw [translate_eq_mul, MonObj.comp_one, _root_.one_mul]

instance (a : 𝟙_ (Over (Spec (CommRingCat.of kb))) ⟶ X) : IsIso (translate X a) :=
  ⟨⟨translate X a⁻¹, by rw [translate_comp_translate, inv_mul_cancel, translate_one],
    by rw [translate_comp_translate, mul_inv_cancel, translate_one]⟩⟩

theorem one_of_comp_translate (a : 𝟙_ (Over (Spec (CommRingCat.of kb))) ⟶ X)
    (p : 𝟙_ (Over (Spec (CommRingCat.of kb))) ⟶ X) (h : p ≫ translate X a = p) : a = 1 := by
  rw [comp_translate, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp] at h
  exact mul_eq_right.mp h

end Translate

section Automorphism

variable {X : Over (Spec (CommRingCat.of kb))} (f : X ⟶ X) [IsIso f] {y : X.left}
  (hy : f.left y = y)

theorem gammaEvaluation_congr {Y : Scheme} {x x' : Y} (h : x = x') :
    Y.Γevaluation x ≫ (Y.residueFieldCongr h).hom = Y.Γevaluation x' := by
  subst h; simp [Scheme.residueFieldCongr_refl]

/-- The automorphism of `κ(y)` induced by an automorphism `f` of `X` fixing `y`. -/
def fieldMap : X.left.residueField y ⟶ X.left.residueField y :=
  (X.left.residueFieldCongr hy.symm).hom ≫ f.left.residueFieldMap y

instance : IsIso (fieldMap f hy) := by
  unfold fieldMap; infer_instance

omit [IsIso f] in
theorem algebraMap_comp_fieldMap :
    CommRingCat.ofHom (algebraMap kb (X.left.residueField y)) ≫ fieldMap f hy =
      CommRingCat.ofHom (algebraMap kb (X.left.residueField y)) := by
  rw [algebraMap_residue_eq, residueAlgHom, CommRingCat.ofHom_hom, fieldMap]
  simp only [Category.assoc]
  rw [reassoc_of% (gammaEvaluation_congr hy.symm), Scheme.Γevaluation_naturality,
    ← Category.assoc X.hom.appTop, ← Scheme.Hom.comp_appTop, Over.w f]

omit [IsIso f] in
theorem fieldMap_algebraMap (c : kb) :
    (fieldMap f hy).hom (algebraMap kb (X.left.residueField y) c) =
      algebraMap kb (X.left.residueField y) c :=
  congrArg (fun g => CommRingCat.Hom.hom g c) (algebraMap_comp_fieldMap f hy)

omit [IsIso f] in
theorem spec_fieldMap :
    Spec.map (fieldMap f hy) ≫ X.left.fromSpecResidueField y =
      X.left.fromSpecResidueField y ≫ f.left := by
  rw [fieldMap, Spec.map_comp, Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField,
    Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]

/-- `fieldMap` as a `kb`-algebra automorphism of `κ(y)`. -/
def fieldEquiv : X.left.residueField y ≃ₐ[kb] X.left.residueField y :=
  AlgEquiv.ofRingEquiv (f := (asIso (fieldMap f hy)).commRingCatIsoToRingEquiv)
    (fieldMap_algebraMap f hy)

theorem fieldEquiv_apply (z : X.left.residueField y) :
    fieldEquiv f hy z = (fieldMap f hy).hom z := rfl

end Automorphism

section Valuative

variable {X : Over (Spec (CommRingCat.of kb))} (f : X ⟶ X)

/-- The residue map `Q → kb` of a degree-one place. -/
theorem exists_residue_retraction {K : Type u} [Field K] [Algebra kb K] (Q : ValuationSubring K)
    (hQ : IsDegreeOnePlace kb Q) :
    ∃ (ι0 : kb →+* Q) (ρ : Q →+* kb), (∀ c, (ι0 c : K) = algebraMap kb K c) ∧
      ρ.comp ι0 = RingHom.id kb ∧ ∀ z : Q, ∃ c : kb, z - ι0 c ∈ IsLocalRing.maximalIdeal Q ∧
        ρ z = c := by
  obtain ⟨hconst, -, hres⟩ := hQ
  let ι0 : kb →+* Q := (algebraMap kb K).codRestrict Q hconst
  let e : kb →+* IsLocalRing.ResidueField Q := (IsLocalRing.residue Q).comp ι0
  have hdeg : ∀ z : Q, ∃ c : kb, z - ι0 c ∈ IsLocalRing.maximalIdeal Q := by
    intro z
    obtain ⟨c, hc⟩ := hres z z.2
    exact ⟨c, ValuationSubring.coe_mem_nonunits_iff.mp hc⟩
  have he : Function.Bijective e := by
    refine ⟨e.injective, fun r => ?_⟩
    obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective r
    obtain ⟨c, hc⟩ := hdeg z
    refine ⟨c, ?_⟩
    show IsLocalRing.residue Q (ι0 c) = IsLocalRing.residue Q z
    exact (Ideal.Quotient.eq).mpr (by
      rw [← neg_sub]; exact neg_mem hc)
  let ρ : Q →+* kb := (RingEquiv.ofBijective e he).symm.toRingHom.comp (IsLocalRing.residue Q)
  have hρι : ρ.comp ι0 = RingHom.id kb := by
    ext c
    show (RingEquiv.ofBijective e he).symm (e c) = c
    rw [← RingEquiv.ofBijective_apply e he, RingEquiv.symm_apply_apply]
  refine ⟨ι0, ρ, fun c => rfl, hρι, fun z => ?_⟩
  obtain ⟨c, hc⟩ := hdeg z
  refine ⟨c, hc, ?_⟩
  have : IsLocalRing.residue Q z = IsLocalRing.residue Q (ι0 c) := (Ideal.Quotient.eq).mpr hc
  show (RingEquiv.ofBijective e he).symm (IsLocalRing.residue Q z) = c
  rw [this]
  show (RingEquiv.ofBijective e he).symm (e c) = c
  rw [← RingEquiv.ofBijective_apply e he, RingEquiv.symm_apply_apply]

theorem not_isUnit_map {K : Type u} [Field K] (Q : ValuationSubring K) (φ : K →+* K)
    (hmem : ∀ z, φ z ∈ Q ↔ z ∈ Q) (φQ : Q →+* Q) (hφQ : ∀ z : Q, (φQ z : K) = φ z) (w : Q)
    (hw : ¬ IsUnit w) : ¬ IsUnit (φQ w) := by
  rintro ⟨u, hu⟩
  apply hw
  have h1 : (φQ w : K) * ((u⁻¹ : Qˣ) : Q) = 1 := by
    rw [← hu]; exact congrArg Subtype.val u.mul_inv
  rw [hφQ] at h1
  have hw0 : (w : K) ≠ 0 := by
    intro h0; rw [h0, map_zero, zero_mul] at h1; exact zero_ne_one h1
  have hinv : ((u⁻¹ : Qˣ) : Q) = φ (w : K)⁻¹ := by
    rw [map_inv₀]; exact (eq_inv_of_mul_eq_one_right h1)
  have hmemw : (w : K)⁻¹ ∈ Q := (hmem _).mp (hinv ▸ ((u⁻¹ : Qˣ) : Q).2)
  exact isUnit_iff_exists_inv.mpr ⟨⟨_, hmemw⟩, Subtype.ext (by simp [hw0])⟩

variable [UniversallyClosed X.hom] [IsSeparated X.hom]

/-- **Fixed place ⇒ fixed point**, for a field `K` with a point `j : Spec K → X` over `kb` and a
`kb`-automorphism `φ` of `K` that `f` lifts: if `φ` maps a degree-one place `Q` of `K/kb` onto
itself, then `f` fixes a `kb`-point of `X` (the centre of `Q`). -/
theorem exists_fixed_point_of_comap_eq {K : Type u} [Field K] [Algebra kb K]
    (j : Spec (CommRingCat.of K) ⟶ X.left)
    (hj : j ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap kb K))) (φ : K ≃ₐ[kb] K)
    (hφ : Spec.map (CommRingCat.ofHom (φ : K →+* K)) ≫ j = j ≫ f.left)
    (Q : ValuationSubring K) (hQ : IsDegreeOnePlace kb Q) (hfix : Q.comap (φ : K →+* K) = Q) :
    ∃ P : 𝟙_ (Over (Spec (CommRingCat.of kb))) ⟶ X, P ≫ f = P := by
  obtain ⟨ι0, ρ, hι0, hρι, hρ⟩ := exists_residue_retraction Q hQ
  have hmem : ∀ z, φ z ∈ Q ↔ z ∈ Q := fun z => by
    conv_rhs => rw [← hfix]
    rfl
  let φQ : Q →+* Q := ((φ : K →+* K).comp Q.subtype).codRestrict Q (fun z => (hmem z).mpr z.2)
  have hφQ : ∀ z : Q, (φQ z : K) = φ z := fun z => rfl
  let i₂ : Spec (CommRingCat.of Q) ⟶ Spec (CommRingCat.of kb) := Spec.map (CommRingCat.ofHom ι0)
  have hι : (algebraMap Q K).comp ι0 = algebraMap kb K := by
    ext c; exact hι0 c
  have sq1 : CommSq j (Spec.map (CommRingCat.ofHom (algebraMap Q K))) X.hom i₂ :=
    ⟨by rw [hj, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hι]⟩
  have sq2 : CommSq (j ≫ f.left) (Spec.map (CommRingCat.ofHom (algebraMap Q K))) X.hom i₂ :=
    ⟨by rw [Category.assoc, Over.w f]; exact sq1.w⟩
  have hE : ValuativeCriterion.Existence X.hom := by
    have h : UniversallyClosed X.hom := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  have hU : ValuativeCriterion.Uniqueness X.hom := by
    have h : IsSeparated X.hom := inferInstance
    rw [IsSeparated.eq_valuativeCriterion] at h
    exact h.1
  obtain ⟨⟨ℓ, hl1, hl2⟩⟩ := (hE ⟨Q, K, j, i₂, sq1⟩).exists_lift
  change Spec.map (CommRingCat.ofHom (algebraMap Q K)) ≫ ℓ = j at hl1
  change ℓ ≫ X.hom = i₂ at hl2
  have hφQι : φQ.comp ι0 = ι0 := by
    ext c
    show φ (ι0 c : K) = (ι0 c : K)
    rw [hι0]; exact φ.commutes c
  have hcomm : CommRingCat.ofHom φQ ≫ CommRingCat.ofHom (algebraMap Q K) =
      CommRingCat.ofHom (algebraMap Q K) ≫ CommRingCat.ofHom (φ : K →+* K) := by
    ext z; rfl
  let L1 : sq2.LiftStruct := ⟨ℓ ≫ f.left, by rw [← Category.assoc, hl1],
    by rw [Category.assoc, Over.w f, hl2]⟩
  let L2 : sq2.LiftStruct := ⟨Spec.map (CommRingCat.ofHom φQ) ≫ ℓ, by
      rw [← Category.assoc, ← Spec.map_comp, hcomm, Spec.map_comp, Category.assoc, hl1]
      exact hφ,
    by rw [Category.assoc, hl2, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hφQι]⟩
  have hL : L1 = L2 := (hU ⟨Q, K, j ≫ f.left, i₂, sq2⟩).elim L1 L2
  have hℓ : ℓ ≫ f.left = Spec.map (CommRingCat.ofHom φQ) ≫ ℓ :=
    congrArg CommSq.LiftStruct.l hL
  have hρφ : ρ.comp φQ = ρ := by
    ext z
    obtain ⟨c, hc, hzc⟩ := hρ z
    obtain ⟨c', hc', hzc'⟩ := hρ (φQ z)
    show ρ (φQ z) = ρ z
    rw [hzc, hzc']
    have h1 : φQ z - ι0 c ∈ IsLocalRing.maximalIdeal Q := by
      have h2 : φQ (z - ι0 c) ∈ IsLocalRing.maximalIdeal Q :=
        not_isUnit_map Q (φ : K →+* K) hmem φQ hφQ _ hc
      rwa [map_sub, show φQ (ι0 c) = ι0 c from congrArg (fun g => g c) hφQι] at h2
    have h3 : ι0 c - ι0 c' ∈ IsLocalRing.maximalIdeal Q := by
      have := Ideal.sub_mem _ hc' h1
      rwa [sub_sub_sub_cancel_left] at this
    by_contra hne
    apply (IsLocalRing.maximalIdeal.isMaximal Q).ne_top
    rw [Ideal.eq_top_iff_one]
    have hu : IsUnit (ι0 c - ι0 c') := by
      rw [← map_sub]; exact (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hne))).map ι0
    have := Ideal.mul_mem_left _ (↑(hu.unit⁻¹) : Q) h3
    rwa [IsUnit.val_inv_mul] at this
  refine ⟨Over.homMk (Spec.map (CommRingCat.ofHom ρ) ≫ ℓ) ?_, ?_⟩
  · show (Spec.map (CommRingCat.ofHom ρ) ≫ ℓ) ≫ X.hom = 𝟙 _
    rw [Category.assoc, hl2, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρι]
    exact Spec.map_id _
  · apply Over.OverMorphism.ext
    show (Spec.map (CommRingCat.ofHom ρ) ≫ ℓ) ≫ f.left = Spec.map (CommRingCat.ofHom ρ) ≫ ℓ
    rw [Category.assoc, hℓ, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρφ]

end Valuative

end TranslationNoFixedPlace

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open TranslationNoFixedPlace

universe u

variable {kb : Type u} [Field kb]

section Main

variable {X : Over (Spec (CommRingCat.of kb))} [UniversallyClosed X.hom] [IsSeparated X.hom]

/-- An automorphism of `X/kb` without `kb`-fixed points, fixing a point `y`, induces a
`kb`-automorphism of `κ(y)` that fixes no degree-one place of `κ(y)/kb`. -/
theorem noFixedDegreeOnePlace_of_noFixedPoint (f : X ⟶ X) [IsIso f]
    (hf : ∀ P : 𝟙_ (Over (Spec (CommRingCat.of kb))) ⟶ X, P ≫ f ≠ P) {y : X.left}
    (hy : f.left y = y) (Q : ValuationSubring (X.left.residueField y))
    (hQ : IsDegreeOnePlace kb Q) :
    Q.comap ((fieldEquiv f hy : X.left.residueField y ≃ₐ[kb] X.left.residueField y) :
      X.left.residueField y →+* X.left.residueField y) ≠ Q := by
  intro hfix
  obtain ⟨P, hP⟩ := exists_fixed_point_of_comap_eq (K := X.left.residueField y) f
    (X.left.fromSpecResidueField y)
    (fromSpecResidueField_hom X y) (fieldEquiv f hy) (spec_fieldMap f hy) Q hQ hfix
  exact hf P hP

variable [GrpObj X]

/-- **The translation hypothesis.** The translation by a `kb`-point `a ≠ 1` of a universally
closed separated group scheme `X/kb` fixes no degree-one place of `κ(y)/kb`, for every point `y`
it fixes. -/
theorem translation_noFixedDegreeOnePlace (a : 𝟙_ (Over (Spec (CommRingCat.of kb))) ⟶ X)
    (ha : a ≠ 1) {y : X.left} (hy : (translate X a).left y = y)
    (Q : ValuationSubring (X.left.residueField y)) (hQ : IsDegreeOnePlace kb Q) :
    Q.comap ((fieldEquiv (translate X a) hy :
      X.left.residueField y ≃ₐ[kb] X.left.residueField y) :
        X.left.residueField y →+* X.left.residueField y) ≠ Q :=
  noFixedDegreeOnePlace_of_noFixedPoint (translate X a)
    (fun P hP => ha (one_of_comp_translate a P hP)) hy Q hQ

/-- The translation hypothesis in the form taken by the group-curve lemma: a `kb`-automorphism of
`κ(y)` fixing no degree-one place. -/
theorem exists_noFixedPlace_of_translation (a : 𝟙_ (Over (Spec (CommRingCat.of kb))) ⟶ X)
    (ha : a ≠ 1) {y : X.left} (hy : (translate X a).left y = y) :
    ∃ σ : X.left.residueField y ≃ₐ[kb] X.left.residueField y,
      ∀ Q : ValuationSubring (X.left.residueField y), IsDegreeOnePlace kb Q →
        Q.comap (σ : X.left.residueField y →+* X.left.residueField y) ≠ Q :=
  ⟨fieldEquiv (translate X a) hy, translation_noFixedDegreeOnePlace a ha hy⟩

end Main

/-- A `kb`-point `a ≠ 1` whose translation fixes `y` (supplied for the generic point of a
component through the unit by `TranslationNoFixedPlace.translationInput_of_component`). -/
def TranslationInput (X : Over (Spec (CommRingCat.of kb))) [GrpObj X] (y : X.left) : Prop :=
  ∃ a : 𝟙_ (Over (Spec (CommRingCat.of kb))) ⟶ X, a ≠ 1 ∧ (translate X a).left y = y

section BaseChange

variable {S : Scheme.{u}} (G : Over S) [GrpObj G] [IsProper G.hom]
  (g : Spec (CommRingCat.of kb) ⟶ S)

/-- **Base change.** For a proper group scheme `G/S` and any `g : Spec kb → S` (for instance a
geometric point of the base of a proper group model), the translation of the fibre
`G ×_S Spec kb` by a `kb`-point `a ≠ 1` fixing `y` gives a `kb`-automorphism of `κ(y)` fixing no
degree-one place. -/
theorem exists_noFixedPlace_baseChange :
    letI : GrpObj ((Over.pullback g).obj G) := Functor.grpObjObj
    ∀ (y : ((Over.pullback g).obj G).left), TranslationInput ((Over.pullback g).obj G) y →
      ∃ σ : ((Over.pullback g).obj G).left.residueField y ≃ₐ[kb]
          ((Over.pullback g).obj G).left.residueField y,
        ∀ Q : ValuationSubring (((Over.pullback g).obj G).left.residueField y),
          IsDegreeOnePlace kb Q →
            Q.comap (σ : ((Over.pullback g).obj G).left.residueField y →+*
              ((Over.pullback g).obj G).left.residueField y) ≠ Q := by
  let _ : GrpObj ((Over.pullback g).obj G) := Functor.grpObjObj
  intro y ⟨a, ha, hy⟩
  have : IsProper ((Over.pullback g).obj G).hom := by
    simp only [Over.pullback_obj_hom]; infer_instance
  exact exists_noFixedPlace_of_translation a ha hy

end BaseChange

section GroupCurve

/-- **Assembly with the group-curve lemma.** Let `K/k` have transcendence degree at most one and
`P` be a degree-one place. Let `X` be a universally closed separated group scheme over an
algebraically closed algebraic extension `kb` of `k`, and `y` a point of `X` such that `κ(y)` is
generated over `kb` by `K` (the function field of the geometric curve). If some translation by a
`kb`-point `a ≠ 1` fixes `y`, no function on `K` has polar divisor exactly `1·P`. -/
theorem not_hasSimplePoleOnlyAt_of_translation {k K : Type*} [Field k] [Field K] [Algebra k K]
    [IsAlgClosed kb] [Algebra k kb] [Algebra.IsAlgebraic k kb]
    {X : Over (Spec (CommRingCat.of kb))} [GrpObj X] [UniversallyClosed X.hom]
    [IsSeparated X.hom] {y : X.left} [Algebra K (X.left.residueField y)]
    [Algebra k (X.left.residueField y)] [IsScalarTower k kb (X.left.residueField y)]
    [IsScalarTower k K (X.left.residueField y)]
    (hgen : IntermediateField.adjoin kb
      (Set.range (algebraMap K (X.left.residueField y))) = ⊤)
    (htr : TrdegLeOne k K) {P : ValuationSubring K} (hP : IsDegreeOnePlace k P)
    (ht : TranslationInput X y) (f : K) : ¬ HasSimplePoleOnlyAt k P f := by
  obtain ⟨a, ha, hy⟩ := ht
  exact not_hasSimplePoleOnlyAt_of_baseChange hgen htr hP (fieldEquiv (translate X a) hy)
    (translation_noFixedDegreeOnePlace a ha hy) f

end GroupCurve

namespace TranslationNoFixedPlace

/-- A closed point of a scheme locally of finite type over an algebraically closed field `kb` is
the image of a `kb`-point. -/
theorem exists_point_of_isClosed [IsAlgClosed kb] {X : Over (Spec (CommRingCat.of kb))}
    [LocallyOfFiniteType X.hom] (x : X.left) (hx : IsClosed {x}) :
    ∃ s : 𝟙_ (Over (Spec (CommRingCat.of kb))) ⟶ X,
      s.left (IsLocalRing.closedPoint kb) = x := by
  let 𝒰 := X.left.affineOpenCover
  let i := 𝒰.idx x
  let R := 𝒰.X i
  let c : Spec R ⟶ X.left := 𝒰.f i
  obtain ⟨p, hp⟩ : ∃ p, c p = x := 𝒰.covers x
  have hc : IsOpenImmersion c := 𝒰.map_prop i
  let φ : CommRingCat.of kb ⟶ R := Spec.preimage (c ≫ X.hom)
  have hφ : Spec.map φ = c ≫ X.hom := Spec.map_preimage _
  have hft : φ.hom.FiniteType := by
    have : LocallyOfFiniteType (Spec.map φ) := by rw [hφ]; infer_instance
    exact HasRingHomProperty.Spec_iff.mp this
  have hpc : IsClosed {p} := by
    have : c ⁻¹' {x} = {p} := by
      ext q
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro hq; exact c.isOpenEmbedding.injective (hq.trans hp.symm)
      · rintro rfl; exact hp
    rw [← this]; exact hx.preimage c.continuous
  have hmax : p.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).mp hpc
  let _ : Algebra kb R := φ.hom.toAlgebra
  have : Algebra.FiniteType kb R := hft
  let _ : Field (R ⧸ p.asIdeal) := Ideal.Quotient.field p.asIdeal
  have : Algebra.FiniteType kb (R ⧸ p.asIdeal) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ kb p.asIdeal)
      (Ideal.Quotient.mkₐ_surjective kb p.asIdeal)
  have : Module.Finite kb (R ⧸ p.asIdeal) := finite_of_finite_type_of_isJacobsonRing kb _
  have hb : Function.Bijective (algebraMap kb (R ⧸ p.asIdeal)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e := RingEquiv.ofBijective (algebraMap kb (R ⧸ p.asIdeal)) hb
  let ψ : R →+* kb := e.symm.toRingHom.comp (Ideal.Quotient.mk p.asIdeal)
  have hψφ : ψ.comp φ.hom = RingHom.id kb := by
    ext a
    show e.symm (Ideal.Quotient.mk p.asIdeal (algebraMap kb R a)) = a
    rw [← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    exact e.symm_apply_apply a
  have hker : RingHom.ker ψ = p.asIdeal := by
    ext r
    rw [RingHom.mem_ker]
    show e.symm (Ideal.Quotient.mk p.asIdeal r) = 0 ↔ r ∈ p.asIdeal
    rw [map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]
  refine ⟨Over.homMk (Spec.map (CommRingCat.ofHom ψ) ≫ c) ?_, ?_⟩
  · show (Spec.map (CommRingCat.ofHom ψ) ≫ c) ≫ X.hom = 𝟙 _
    rw [Category.assoc, ← hφ, ← Spec.map_comp]
    have : φ ≫ CommRingCat.ofHom ψ = 𝟙 _ := by
      ext a; exact congrArg (fun g => g a) hψφ
    exact (congrArg Spec.map this).trans (Spec.map_id _)
  · show c ((Spec.map (CommRingCat.ofHom ψ)) (IsLocalRing.closedPoint kb)) = x
    have : (Spec.map (CommRingCat.ofHom ψ)) (IsLocalRing.closedPoint kb) = p := by
      apply PrimeSpectrum.ext
      show Ideal.comap ψ (IsLocalRing.maximalIdeal kb) = p.asIdeal
      rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot, hker]
    rw [this]; exact hp

/-- A homeomorphism maps irreducible components to irreducible components. -/
theorem image_mem_irreducibleComponents {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (h : α ≃ₜ β) {Z : Set α} (hZ : Z ∈ irreducibleComponents α) :
    h '' Z ∈ irreducibleComponents β := by
  refine ⟨hZ.1.image h h.continuous.continuousOn, fun T hT hsub => ?_⟩
  have h1 : IsIrreducible (h.symm '' T) := hT.image h.symm h.symm.continuous.continuousOn
  have h2 : Z ⊆ h.symm '' T := by
    intro z hz
    exact ⟨h z, hsub ⟨z, hz, rfl⟩, h.symm_apply_apply z⟩
  have h3 := hZ.2 h1 h2
  intro t ht
  exact ⟨h.symm t, h3 ⟨t, ht, rfl⟩, h.apply_symm_apply t⟩

/-- The unit point of a group scheme over `kb`. -/
def unitPoint (X : Over (Spec (CommRingCat.of kb))) [GrpObj X] : X.left :=
  (MonObj.one : 𝟙_ (Over (Spec (CommRingCat.of kb))) ⟶ X).left (IsLocalRing.closedPoint kb)

/-- **The translation input.** Let `X` be a proper group scheme over an algebraically closed field
`kb` and `y` the generic point of an irreducible component through the unit. If `y` is not a closed
point, some `kb`-point `a ≠ 1` has a translation fixing `y`. -/
theorem translationInput_of_component [IsAlgClosed kb] {X : Over (Spec (CommRingCat.of kb))}
    [GrpObj X] [IsProper X.hom] (y : X.left) (hcomp : closure {y} ∈ irreducibleComponents X.left)
    (he : y ⤳ unitPoint X) (hy : ¬ IsClosed {y}) : TranslationInput X y := by
  classical
  have : TopologicalSpace.NoetherianSpace X.left := by
    have := LocallyOfFiniteType.isLocallyNoetherian X.hom
    have := QuasiCompact.compactSpace_of_compactSpace X.hom
    have : IsNoetherian X.left := {}
    infer_instance
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  set Z := closure ({y} : Set X.left)
  let O : Set X.left := ⋃₀ (irreducibleComponents X.left \ {Z})
  have hO : IsClosed O :=
    (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.sdiff).isClosed_sUnion
      (fun t ht => isClosed_of_mem_irreducibleComponents t ht.1)
  have hyO : y ∉ O := by
    rintro ⟨T, ⟨hT, hTZ⟩, hyT⟩
    apply hTZ
    have hZT : Z ⊆ T :=
      (isClosed_of_mem_irreducibleComponents T hT).closure_subset_iff.mpr
        (Set.singleton_subset_iff.mpr hyT)
    exact (hcomp.2 hT.1 hZT).antisymm hZT
  -- a closed point of `Oᶜ` other than the unit
  have hloc : IsLocallyClosed Oᶜ := hO.isOpen_compl.isLocallyClosed
  have hdense := JacobsonSpace.closure_inter_closedPoints_eq_closure hloc
  have hex : ∃ a ∈ Oᶜ ∩ closedPoints X.left, a ≠ unitPoint X := by
    by_contra hne
    push Not at hne
    have hsub : Oᶜ ∩ closedPoints X.left ⊆ {unitPoint X} := fun a ha => hne a ha
    have hyc : y ∈ closure (Oᶜ ∩ closedPoints X.left) := by
      rw [hdense]; exact subset_closure hyO
    obtain ⟨a, ha⟩ : (Oᶜ ∩ closedPoints X.left).Nonempty := by
      by_contra hem
      rw [Set.not_nonempty_iff_eq_empty] at hem
      rw [hem, closure_empty] at hyc
      exact hyc
    have hae : a = unitPoint X := hne a ha
    have hec : IsClosed {unitPoint X} := hae ▸ ha.2
    have := closure_mono hsub hyc
    rw [hec.closure_eq, Set.mem_singleton_iff] at this
    exact hy (this ▸ hec)
  obtain ⟨a, ⟨haO, hac⟩, hae⟩ := hex
  obtain ⟨s, hs⟩ := exists_point_of_isClosed a hac
  refine ⟨s, ?_, ?_⟩
  · rintro rfl
    exact hae hs.symm
  · -- the translation maps the component `Z` onto itself
    have : IsIso (translate X s).left :=
      inferInstanceAs (IsIso ((Over.forget _).map (translate X s)))
    let h := (translate X s).left.homeomorph
    have key : (MonObj.one : 𝟙_ (Over (Spec (CommRingCat.of kb))) ⟶ X) ≫ translate X s = s := by
      have h1 : (MonObj.one : 𝟙_ (Over (Spec (CommRingCat.of kb))) ⟶ X) = 1 := by
        rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
      rw [comp_translate, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp, h1, _root_.mul_one]
    have hhe : h (unitPoint X) = a := by
      rw [Scheme.Hom.homeomorph_apply]
      show ((MonObj.one : 𝟙_ (Over (Spec (CommRingCat.of kb))) ⟶ X) ≫ translate X s).left
        (IsLocalRing.closedPoint kb) = a
      rw [key]; exact hs
    have heZ : unitPoint X ∈ Z := specializes_iff_mem_closure.mp he
    have hZ' : h '' Z ∈ irreducibleComponents X.left := image_mem_irreducibleComponents h hcomp
    have hZZ : h '' Z = Z := by
      by_contra hne
      exact haO ⟨h '' Z, ⟨hZ', hne⟩, hhe ▸ ⟨_, heZ, rfl⟩⟩
    have hcl : closure {h y} = closure {y} := by
      rw [← Set.image_singleton, ← Homeomorph.image_closure, hZZ]
    have := (inseparable_iff_closure_eq.mpr hcl).eq
    rwa [Scheme.Hom.homeomorph_apply] at this

/-- At a closed point of a scheme locally of finite type over an algebraically closed field `kb`,
the residue field is `kb`. -/
theorem algebraMap_residue_surjective_of_isClosed [IsAlgClosed kb]
    {X : Over (Spec (CommRingCat.of kb))} [LocallyOfFiniteType X.hom] (y : X.left)
    (hy : IsClosed {y}) : Function.Surjective (algebraMap kb (X.left.residueField y)) := by
  obtain ⟨s, hs⟩ := exists_point_of_isClosed y hy
  let t : Spec (CommRingCat.of kb) ⟶ X.left := s.left
  have ht : t ≫ X.hom = 𝟙 _ := Over.w s
  let x0 : Spec (CommRingCat.of kb) := IsLocalRing.closedPoint kb
  have hs' : t x0 = y := hs
  let g := (X.left.residueFieldCongr hs'.symm).hom ≫ t.residueFieldMap x0
  have hcomp : CommRingCat.ofHom (algebraMap kb (X.left.residueField y)) ≫ g =
      (Scheme.ΓSpecIso (CommRingCat.of kb)).inv ≫ (Spec (CommRingCat.of kb)).Γevaluation x0 := by
    rw [algebraMap_residue_eq, residueAlgHom, CommRingCat.ofHom_hom]
    simp only [g, Category.assoc]
    rw [reassoc_of% (gammaEvaluation_congr hs'.symm), Scheme.Γevaluation_naturality,
      ← Category.assoc X.hom.appTop, ← Scheme.Hom.comp_appTop, ht, Scheme.Hom.id_appTop,
      Category.id_comp]
  have hbij : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of kb)).inv ≫
      (Spec (CommRingCat.of kb)).Γevaluation x0).hom :=
    (asIso ((Scheme.ΓSpecIso (CommRingCat.of kb)).inv ≫
      (Spec (CommRingCat.of kb)).Γevaluation x0)).commRingCatIsoToRingEquiv.bijective
  intro z
  obtain ⟨c, hc⟩ := hbij.2 (g.hom z)
  refine ⟨c, g.hom.injective ?_⟩
  rw [← hc, ← hcomp]
  rfl

end TranslationNoFixedPlace

section Component

variable [IsAlgClosed kb]

/-- **The translation hypothesis for a component.** For a proper group scheme `X` over an
algebraically closed field `kb` and the generic point `y` of an irreducible component through the
unit, `y` not closed, there is a `kb`-automorphism of `κ(y)` fixing no degree-one place. -/
theorem exists_noFixedPlace_of_component {X : Over (Spec (CommRingCat.of kb))} [GrpObj X]
    [IsProper X.hom] (y : X.left) (hcomp : closure {y} ∈ irreducibleComponents X.left)
    (he : y ⤳ unitPoint X) (hy : ¬ IsClosed {y}) :
    ∃ σ : X.left.residueField y ≃ₐ[kb] X.left.residueField y,
      ∀ Q : ValuationSubring (X.left.residueField y), IsDegreeOnePlace kb Q →
        Q.comap (σ : X.left.residueField y →+* X.left.residueField y) ≠ Q := by
  obtain ⟨a, ha, hya⟩ := translationInput_of_component y hcomp he hy
  exact exists_noFixedPlace_of_translation a ha hya

variable {S : Scheme.{u}} (G : Over S) [GrpObj G] [IsProper G.hom]
  (g : Spec (CommRingCat.of kb) ⟶ S)

/-- The same for the fibre `G ×_S Spec kb` of a proper group scheme `G/S` along any
`g : Spec kb → S` (for instance a geometric point of the base of a proper group model). -/
theorem exists_noFixedPlace_baseChange_of_component :
    letI : GrpObj ((Over.pullback g).obj G) := Functor.grpObjObj
    ∀ (y : ((Over.pullback g).obj G).left),
      closure {y} ∈ irreducibleComponents ((Over.pullback g).obj G).left →
      y ⤳ unitPoint ((Over.pullback g).obj G) → ¬ IsClosed {y} →
      ∃ σ : ((Over.pullback g).obj G).left.residueField y ≃ₐ[kb]
          ((Over.pullback g).obj G).left.residueField y,
        ∀ Q : ValuationSubring (((Over.pullback g).obj G).left.residueField y),
          IsDegreeOnePlace kb Q →
            Q.comap (σ : ((Over.pullback g).obj G).left.residueField y →+*
              ((Over.pullback g).obj G).left.residueField y) ≠ Q := by
  let _ : GrpObj ((Over.pullback g).obj G) := Functor.grpObjObj
  intro y hcomp he hy
  have : IsProper ((Over.pullback g).obj G).hom := by
    simp only [Over.pullback_obj_hom]; infer_instance
  exact exists_noFixedPlace_of_component y hcomp he hy

end Component

section Assembly

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsAlgClosed kb] [Algebra k kb]
  [Algebra.IsAlgebraic k kb] {X : Over (Spec (CommRingCat.of kb))} {y : X.left}
  [Algebra K (X.left.residueField y)] [Algebra k (X.left.residueField y)]
  [IsScalarTower k kb (X.left.residueField y)] [IsScalarTower k K (X.left.residueField y)]

/-- If `κ(y)` contains a field `K` with a degree-one place over `k`, then `y` is not a closed
point. -/
theorem not_isClosed_of_isDegreeOnePlace [LocallyOfFiniteType X.hom] {P : ValuationSubring K}
    (hP : IsDegreeOnePlace k P) : ¬ IsClosed {y} := by
  intro hy
  apply hP.2.1
  rw [eq_top_iff]
  intro x _
  obtain ⟨c, hc⟩ := algebraMap_residue_surjective_of_isClosed y hy
    (algebraMap K (X.left.residueField y) x)
  have h1 : IsIntegral k (algebraMap kb (X.left.residueField y) c) :=
    ((Algebra.IsAlgebraic.isAlgebraic (R := k) c).isIntegral).map
      (IsScalarTower.toAlgHom k kb (X.left.residueField y))
  rw [hc] at h1
  have h2 : IsIntegral k x :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom k K (X.left.residueField y))
      (algebraMap K (X.left.residueField y)).injective).mp h1
  exact GroupCurveNotP1.mem_of_isIntegral P hP.1 h2

/-- **N9-bridge B3, assembled.** Let `K/k` have transcendence degree at most one with a degree-one
place `P`; let `X` be a proper group scheme over an algebraically closed algebraic extension `kb`
of `k`, and `y` the generic point of an irreducible component of `X` through the unit, such that
`κ(y)` is generated over `kb` by `K`. Then no function on `K` has polar divisor exactly `1·P`. -/
theorem not_hasSimplePoleOnlyAt_of_component [GrpObj X] [IsProper X.hom]
    (hcomp : closure {y} ∈ irreducibleComponents X.left) (he : y ⤳ unitPoint X)
    (hgen : IntermediateField.adjoin kb
      (Set.range (algebraMap K (X.left.residueField y))) = ⊤)
    (htr : TrdegLeOne k K) {P : ValuationSubring K} (hP : IsDegreeOnePlace k P) (f : K) :
    ¬ HasSimplePoleOnlyAt k P f :=
  not_hasSimplePoleOnlyAt_of_translation hgen htr hP
    (translationInput_of_component y hcomp he (not_isClosed_of_isDegreeOnePlace hP)) f

end Assembly

end ZInQ.Contrib.CMHeight62Full

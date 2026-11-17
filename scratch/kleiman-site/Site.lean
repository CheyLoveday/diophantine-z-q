import ZInQKernel.Contrib.OneProof.KleimanPicZero954

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry Limits Opposite MonoidalCategory

namespace KleimanSite

open Scheme KleimanSection2

variable {S : Scheme.{u}}

/-- Kleiman's fppf precoverage on locally Noetherian `S`-schemes. -/
def fppfPrecoverageLN (S : Scheme.{u}) : Precoverage (LocNoeth S).FullSubcategory :=
  fppfPrecoverage.comap ((LocNoeth S).ι ⋙ Over.forget S)

/-- Kleiman's site. -/
abbrev fppfTopologyLN (S : Scheme.{u}) : GrothendieckTopology (LocNoeth S).FullSubcategory :=
  (fppfPrecoverageLN S).toGrothendieck

lemma prop_of_mem {X : (LocNoeth S).FullSubcategory} {R : Presieve X} (hR : R ∈ fppfPrecoverageLN S X)
    {Y : (LocNoeth S).FullSubcategory} {g : Y ⟶ X} (hg : R g) :
    Flat g.hom.left ∧ LocallyOfFinitePresentation g.hom.left :=
  hR.2 (Presieve.map_map hg)

lemma locNoeth_pullback_of_right {X Y Z : (LocNoeth S).FullSubcategory} (g : Z ⟶ X) (f : Y ⟶ X)
    [LocallyOfFiniteType f.hom.left] : LocNoeth S (pullback g.hom f.hom) := by
  have h : IsPullback (pullback.fst g.hom f.hom).left (pullback.snd g.hom f.hom).left
      g.hom.left f.hom.left := (IsPullback.of_hasPullback g.hom f.hom).map (Over.forget S)
  have : LocallyOfFiniteType (pullback.fst g.hom f.hom).left :=
    MorphismProperty.of_isPullback h ‹_›
  have : IsLocallyNoetherian Z.obj.left := Z.property
  exact LocallyOfFiniteType.isLocallyNoetherian (pullback.fst g.hom f.hom).left

lemma locNoeth_pullback_of_left {X Y Z : (LocNoeth S).FullSubcategory} (g : Z ⟶ X) (f : Y ⟶ X)
    [LocallyOfFiniteType g.hom.left] : LocNoeth S (pullback g.hom f.hom) := by
  have h : IsPullback (pullback.fst g.hom f.hom).left (pullback.snd g.hom f.hom).left
      g.hom.left f.hom.left := (IsPullback.of_hasPullback g.hom f.hom).map (Over.forget S)
  have : LocallyOfFiniteType (pullback.snd g.hom f.hom).left :=
    MorphismProperty.of_isPullback h.flip ‹_›
  have : IsLocallyNoetherian Y.obj.left := Y.property
  exact LocallyOfFiniteType.isLocallyNoetherian (pullback.snd g.hom f.hom).left

/-- The pullback in `Over S`, as a locally Noetherian `S`-scheme. -/
def pbLN {X Y Z : (LocNoeth S).FullSubcategory} (g : Z ⟶ X) (f : Y ⟶ X)
    (h : LocNoeth S (pullback g.hom f.hom)) : (LocNoeth S).FullSubcategory :=
  ⟨pullback g.hom f.hom, h⟩

lemma isPullback_pbLN {X Y Z : (LocNoeth S).FullSubcategory} (g : Z ⟶ X) (f : Y ⟶ X)
    (h : LocNoeth S (pullback g.hom f.hom)) :
    IsPullback (ObjectProperty.homMk (pullback.fst g.hom f.hom) : pbLN g f h ⟶ Z)
      (ObjectProperty.homMk (pullback.snd g.hom f.hom) : pbLN g f h ⟶ Y) g f :=
  IsPullback.of_map (LocNoeth S).ι (by ext1; exact pullback.condition)
    (IsPullback.of_hasPullback g.hom f.hom)

lemma preservesLimit_cospan {X Y Z : (LocNoeth S).FullSubcategory} (g : Z ⟶ X) (f : Y ⟶ X)
    (h : LocNoeth S (pullback g.hom f.hom)) : PreservesLimit (cospan g f) (LocNoeth S).ι :=
  (isPullback_pbLN g f h).preservesLimit_cospan_iff.mpr (IsPullback.of_hasPullback g.hom f.hom)

instance : (fppfPrecoverageLN S).HasPullbacks where
  hasPullbacks_of_mem {X Y R} f hR := by
    refine ⟨fun {Z g} hg ↦ ?_⟩
    have := (prop_of_mem hR hg).2
    exact (isPullback_pbLN g f (locNoeth_pullback_of_left g f)).hasPullback

instance : (fppfPrecoverageLN S).PullbacksPreservedBy (LocNoeth S).ι where
  preservesPairwisePullbacks_of_mem {X R} hR := by
    refine ⟨fun {Y Z f g} hf hg ↦ ?_⟩
    have := (prop_of_mem hR hf).2
    exact preservesLimit_cospan f g (locNoeth_pullback_of_left f g)

instance : (fppfPrecoverageLN S).IsStableUnderBaseChange where
  mem_coverings_of_isPullback {ι} X Y f hf Z g P p₁ p₂ h := by
    have hf' := hf
    simp only [fppfPrecoverageLN, Precoverage.mem_comap_iff, Presieve.map_ofArrows] at hf' ⊢
    refine Precoverage.mem_coverings_of_isPullback _ hf' _ _ _ fun i ↦ ?_
    have := (prop_of_mem hf (Presieve.ofArrows.mk i)).2
    have := preservesLimit_cospan g (f i) (locNoeth_pullback_of_right g (f i))
    exact ((h i).map (LocNoeth S).ι).map (Over.forget S)

instance : (LocNoeth S).ι.IsContinuous (fppfTopologyLN S) (fppfTopology.over S) := by
  rw [over_toGrothendieck_eq_toGrothendieck_comap_forget]
  exact Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy _ _
    (le_of_eq (Precoverage.comap_comp _ _ _))

instance : (LocNoeth S).ι.IsCocontinuous (fppfTopologyLN S) (fppfTopology.over S) where
  cover_lift {T R} hR := by
    rw [GrothendieckTopology.mem_over_iff] at hR
    obtain ⟨R0, hR0, hle⟩ :=
      (Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition (J := fppfPrecoverage)).mp hR
    obtain ⟨ι, Y, f, rfl⟩ := R0.exists_eq_ofArrows
    have hR0' := hR0
    rw [fppfPrecoverage, ofArrows_mem_precoverage_iff] at hR0'
    have hLN : ∀ i, LocNoeth S (Over.mk (f i ≫ T.obj.hom)) := fun i ↦ by
      have : IsLocallyNoetherian T.obj.left := T.property
      have : LocallyOfFinitePresentation (f i) := (hR0'.2 i).2
      exact LocallyOfFiniteType.isLocallyNoetherian (f i)
    let V : ι → (LocNoeth S).FullSubcategory := fun i ↦ ⟨Over.mk (f i ≫ T.obj.hom), hLN i⟩
    let g : ∀ i, V i ⟶ T := fun i ↦ ObjectProperty.homMk (Over.homMk (f i))
    refine GrothendieckTopology.superset_covering _ ?_
      (Precoverage.generate_mem_toGrothendieck (R := Presieve.ofArrows V g) ?_)
    · rw [Sieve.generate_le_iff]
      rintro _ _ ⟨i⟩
      change R (Over.homMk (f i) : Over.mk (f i ≫ T.obj.hom) ⟶ T.obj)
      rw [← Sieve.overEquiv_iff]
      exact hle _ (Presieve.ofArrows.mk i)
    · simp only [fppfPrecoverageLN, Precoverage.mem_comap_iff, Presieve.map_ofArrows]
      exact hR0

/-! ## Kleiman's Picard sheaf on the locally Noetherian site -/

/-- **Kleiman's `Pic_{(X/S)(fppf)}`**: the sheafification, on the site of locally Noetherian `S`-schemes with the
fppf topology, of `T ↦ Pic(X ×_S T)`. -/
def kleimanPicardSheafLN {X : Scheme.{u}} (f : X ⟶ S) : Sheaf (fppfTopologyLN S) (Type (u + 1)) :=
  (presheafToSheaf (fppfTopologyLN S) (Type (u + 1))).obj ((LocNoeth S).ι.op ⋙ picardPresheaf f)

/-- The restriction of `toSheafify` to locally Noetherian test schemes. -/
def restrictToSheafify {X : Scheme.{u}} (f : X ⟶ S) :
    (LocNoeth S).ι.op ⋙ picardPresheaf f ⟶ picardFunctorLN f :=
  Functor.whiskerLeft (LocNoeth S).ι.op (toSheafify (fppfTopology.over S) (picardPresheaf f))

lemma isSheaf_picardFunctorLN {X : Scheme.{u}} (f : X ⟶ S) :
    Presheaf.IsSheaf (fppfTopologyLN S) (picardFunctorLN f) :=
  (LocNoeth S).ι.op_comp_isSheaf _ (fppfTopology.over S) (picardFunctor f)

instance {X : Scheme.{u}} (f : X ⟶ S) :
    Presheaf.IsLocallyInjective (fppfTopologyLN S) (restrictToSheafify f) :=
  Presheaf.isLocallyInjective_whisker _ (fppfTopology.over S) _ _

instance {X : Scheme.{u}} (f : X ⟶ S) :
    Presheaf.IsLocallySurjective (fppfTopologyLN S) (restrictToSheafify f) :=
  Presheaf.isLocallySurjective_whisker _ (fppfTopology.over S) _ _

instance isIso_sheafify_restrictToSheafify {X : Scheme.{u}} (f : X ⟶ S) :
    IsIso ((presheafToSheaf (fppfTopologyLN S) (Type (u + 1))).map (restrictToSheafify f)) :=
  ((fppfTopologyLN S).W_iff _).mp ((fppfTopologyLN S).W_of_isLocallyBijective _)

/-- **The comparison.** Kleiman's sheaf on the locally Noetherian site is the restriction of the tree's
`picardFunctor` (sheafified on all `S`-schemes) to locally Noetherian `S`-schemes. -/
def kleimanIso {X : Scheme.{u}} (f : X ⟶ S) : (kleimanPicardSheafLN f).obj ≅ picardFunctorLN f :=
  (sheafToPresheaf _ _).mapIso (asIso ((presheafToSheaf (fppfTopologyLN S) (Type (u + 1))).map
    (restrictToSheafify f))) ≪≫ (isoSheafify (fppfTopologyLN S) (isSheaf_picardFunctorLN f)).symm

lemma toSheafify_kleimanIso {X : Scheme.{u}} (f : X ⟶ S) :
    toSheafify (fppfTopologyLN S) ((LocNoeth S).ι.op ⋙ picardPresheaf f) ≫ (kleimanIso f).hom =
      restrictToSheafify f := by
  change toSheafify _ _ ≫ sheafifyMap _ (restrictToSheafify f) ≫
    (isoSheafify (fppfTopologyLN S) (isSheaf_picardFunctorLN f)).inv = _
  rw [← toSheafify_naturality_assoc, ← isoSheafify_hom (fppfTopologyLN S) (isSheaf_picardFunctorLN f),
    Iso.hom_inv_id, Category.comp_id]

/-! ## Kleiman 9.5.4 over Kleiman's site -/

/-- **The identity point** of a scheme `P` representing Kleiman's sheaf on the locally Noetherian site: the
`K`-point classifying the class of `𝒪_X`. -/
def unitPtSite {K : Type} [Field K] {X : Over (Spec (CommRingCat.of K))} {P : Over (Spec (CommRingCat.of K))}
    {hP : LocNoeth _ P} (rep : (kleimanPicardSheafLN X.hom).obj.RepresentableBy ⟨P, hP⟩) :
    𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ P :=
  (rep.homEquiv (X := unitLN K)).symm
    ((toSheafify (fppfTopologyLN _) ((LocNoeth _).ι.op ⋙ picardPresheaf X.hom)).app (op (unitLN K))
      (1 : (pullback X.hom (𝟙_ (Over (Spec (CommRingCat.of K)))).hom).Pic)) |>.hom

/-- **The identity component** `Pic⁰` of a scheme representing Kleiman's sheaf. -/
def identityComponentSite {K : Type} [Field K] {X : Over (Spec (CommRingCat.of K))}
    {P : Over (Spec (CommRingCat.of K))} {hP : LocNoeth _ P}
    (rep : (kleimanPicardSheafLN X.hom).obj.RepresentableBy ⟨P, hP⟩) : Set P.left :=
  {x | ∃ s : (𝟙_ (Over (Spec (CommRingCat.of K)))).left, x ∈ connectedComponent ((unitPtSite rep).left s)}

/-- **LEAF (printed form).** Kleiman 9.5.4 over Kleiman's own site. -/
def KleimanPicZeroProper954Site : Prop :=
  ∀ (K : Type) [Field K] (X : Over (Spec (CommRingCat.of K))),
    (∃ (N : Type) (_ : Finite N) (i : X.left ⟶ ℙ(N; Spec (CommRingCat.of K))),
      IsClosedImmersion i ∧ i ≫ ℙ(N; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K) = X.hom) →
    GeometricallyIntegral X.hom → geometrically IsNormalScheme X.hom →
    (∃ σ : Spec (CommRingCat.of K) ⟶ X.left, σ ≫ X.hom = 𝟙 _) →
    ∀ (P : Over (Spec (CommRingCat.of K))) (hP : LocallyOfFiniteType P.hom)
      (rep : (kleimanPicardSheafLN X.hom).obj.RepresentableBy ⟨P, locNoeth_of_lft hP⟩) (V : P.left.Opens),
      (V : Set P.left) = identityComponentSite rep → IsProper (V.ι ≫ P.hom)

/-- A representation of the tree's restricted functor is a representation of Kleiman's sheaf. -/
def repSite {X : Scheme.{u}} {f : X ⟶ S} {P : (LocNoeth S).FullSubcategory}
    (rep : (picardFunctorLN f).RepresentableBy P) : (kleimanPicardSheafLN f).obj.RepresentableBy P :=
  rep.ofIso (kleimanIso f).symm

lemma unitPtSite_repSite {K : Type} [Field K] {X : Over (Spec (CommRingCat.of K))}
    {P : Over (Spec (CommRingCat.of K))} {hP : LocNoeth _ P}
    (rep : (picardFunctorLN X.hom).RepresentableBy ⟨P, hP⟩) : unitPtSite (repSite rep) = unitPt rep := by
  unfold unitPtSite unitPt
  congr 2
  change rep.homEquiv.symm ((kleimanIso X.hom).hom.app _ _) = _
  congr 1
  exact ConcreteCategory.congr_hom (congr_app (toSheafify_kleimanIso X.hom) (op (unitLN K)))
    (1 : (pullback X.hom (𝟙_ (Over (Spec (CommRingCat.of K)))).hom).Pic)

/-- **The derivation**: the tree-site form of the leaf from the Kleiman-site form. -/
theorem kleimanPicZeroProper954_of_site (h : KleimanPicZeroProper954Site) : KleimanPicZeroProper954 := by
  intro K _ X hproj hgi hgn hσ P hP rep V hV
  refine h K X hproj hgi hgn hσ P hP (repSite rep) V ?_
  rw [hV]
  unfold identityComponentSite identityComponentLN
  rw [unitPtSite_repSite]

end KleimanSite

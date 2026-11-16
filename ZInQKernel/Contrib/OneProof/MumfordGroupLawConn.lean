import ZInQKernel.Contrib.OneProof.MumfordRigidity

/-!
# `MumfordRigidity.MumfordGroupLaw` from Mumford's GIT Thm 6.14 over a connected base (task dict-models)

The research field `mumfordGroupLaw` (`ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw`) is GIT Thm 6.14 over any
locally noetherian `S`, "on each connected component". The print assumes `S` connected (as recalled), so the field
is the print plus a gluing argument, which the 11-16 dictionary pass counted against the row.

This file states the leaf with `ConnectedSpace S` added (`MumfordGroupLawConn`) and PROVES the gluing in Lean, so
the field follows with no other input:

* `glue_ext`, `glue_exists`: over a cover of `S` by pairwise disjoint opens `U i`, morphisms in `Over S` are
  determined by, and glued from, their base changes to the `U i` (Mathlib's `Scheme.Cover.glueMorphisms`);
* `grpObj_of_pieces`: group objects `(P i) F` (with `P i = Over.pullback (U i).ι`) glue to a group object structure
  on `F`, built by Yoneda (`GrpObj.ofRepresentableBy`) from the bijection
  `(T ⟶ F) ≃ ∀ i, (P i T ⟶ P i F)`; its identity is the glued identity (`eta_left`);
* `mumfordGroupLaw_of_conn : MumfordGroupLawConn → MumfordGroupLaw`, with the open connected components of the
  locally noetherian `S` (`isOpen_connectedComponent_of_isLocallyNoetherian`, gt-rigidity) as the cover; the
  hypotheses of the leaf pass to each component by base change (proper, smooth, geometrically connected) and by the
  pasting lemma for pullbacks (the abelian-variety fibres).
-/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace DictModels.MumfordConn

open LeafQM.AV.R1UnivRigid PkgI3

/-- **LEAF `MumfordGroupLawConn`** (Mumford–Fogarty–Kirwan, *Geometric Invariant Theory*, 3rd ed., Ch. 6, Thm 6.14;
numbers UNVERIFIED, no network). *Printed* (as recalled): `S` connected and locally noetherian, `F → S` smooth and
proper with a section `e`, one geometric fibre an abelian variety (with origin `e(s)`); then `F` is an abelian scheme
over `S` with identity `e`. *Lean form*: the field `MumfordGroupLaw` word for word with `ConnectedSpace S` added; the
other hypotheses are at least as strong as the print's (geometrically connected fibres, and *every* field fibre an
abelian variety with origin `e(s)`), and the conclusion is the group-object part of "abelian scheme" (a
consequence). -/
def MumfordGroupLawConn : Prop :=
  ∀ (S : Scheme.{0}) (F : Over S) (e : S ⟶ F.left), IsLocallyNoetherian S → ConnectedSpace S →
    IsProper F.hom → Smooth F.hom → GeometricallyConnected F.hom → e ≫ F.hom = 𝟙 S →
    (∀ (K : Type) [Field K] (s : Spec (CommRingCat.of K) ⟶ S),
      ∃ (A : AbVar K) (g : A.X.left ⟶ F.left), IsAbVarFibre F e s A g) →
    ∃ _G : GrpObj F, η[F].left = e

/-- The field implies the new leaf (so the leaf is never stronger than the field). -/
theorem conn_of_field (h : ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw) : MumfordGroupLawConn :=
  fun S F e h1 _ h2 h3 h4 h5 h6 => h S F e h1 h2 h3 h4 h5 h6

/-! ## §1. Gluing morphisms over a disjoint open cover -/

section Glue

variable {S : Scheme.{0}} {ι : Type} (U : ι → S.Opens) (hcov : ∀ s : S, ∃ i, s ∈ U i)
  (hdisj : ∀ i j, i ≠ j → ∀ s : S, s ∈ U i → s ∉ U j)

theorem pbmap_left_fst {i : ι} {X Y : Over S} (f : X ⟶ Y) :
    ((Over.pullback (U i).ι).map f).left ≫ pullback.fst Y.hom (U i).ι =
      pullback.fst X.hom (U i).ι ≫ f.left := by
  simp only [Over.pullback_map_left, pullback.lift_fst]

theorem pbmap_left_snd {i : ι} {X Y : Over S} (f : X ⟶ Y) :
    ((Over.pullback (U i).ι).map f).left ≫ pullback.snd Y.hom (U i).ι = pullback.snd X.hom (U i).ι := by
  simp only [Over.pullback_map_left, pullback.lift_snd]

include hcov in
/-- Morphisms in `Over S` are determined by their base changes to the `U i`. -/
theorem glue_ext {X Y : Over S} (f g : X ⟶ Y)
    (h : ∀ i, (Over.pullback (U i).ι).map f = (Over.pullback (U i).ι).map g) : f = g := by
  apply Over.OverMorphism.ext
  apply Scheme.hom_ext_of_forall
  intro x
  obtain ⟨i, hi⟩ := hcov (X.hom x)
  refine ⟨X.hom ⁻¹ᵁ U i, hi, ?_⟩
  rw [← pullbackRestrictIsoRestrict_inv_fst, Category.assoc, Category.assoc, ← pbmap_left_fst,
    ← pbmap_left_fst, h i]

include hcov hdisj in
/-- Morphisms in `Over S` glue from their base changes to the `U i`. -/
theorem glue_exists {X Y : Over S} (g : ∀ i, (Over.pullback (U i).ι).obj X ⟶ (Over.pullback (U i).ι).obj Y) :
    ∃ f : X ⟶ Y, ∀ i, (Over.pullback (U i).ι).map f = g i := by
  let V : ι → X.left.Opens := fun i => X.hom ⁻¹ᵁ U i
  have hV : IsOpenCover V := by
    rw [IsOpenCover, eq_top_iff]
    intro x _
    obtain ⟨i, hi⟩ := hcov (X.hom x)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  let 𝒰 := X.left.openCoverOfIsOpenCover V hV
  let fi : ∀ i, 𝒰.X i ⟶ Y.left := fun i =>
    (pullbackRestrictIsoRestrict X.hom (U i)).inv ≫ (g i).left ≫ pullback.fst Y.hom (U i).ι
  have hf : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ fi i = pullback.snd _ _ ≫ fi j := by
    intro i j
    by_cases hij : i = j
    · subst hij
      have : pullback.fst (𝒰.f i) (𝒰.f i) = pullback.snd (𝒰.f i) (𝒰.f i) := by
        rw [← cancel_mono (𝒰.f i)]; exact pullback.condition
      rw [this]
    · apply Scheme.hom_ext_of_forall
      intro z
      exfalso
      have hz : (𝒰.f i) (pullback.fst (𝒰.f i) (𝒰.f j) z) = (𝒰.f j) (pullback.snd (𝒰.f i) (𝒰.f j) z) := by
        rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
      have h1 : (𝒰.f i) (pullback.fst (𝒰.f i) (𝒰.f j) z) ∈ V i := by
        have : (V i).ι (pullback.fst (𝒰.f i) (𝒰.f j) z) ∈ Set.range (V i).ι := ⟨_, rfl⟩
        rwa [Scheme.Opens.range_ι] at this
      have h2 : (𝒰.f j) (pullback.snd (𝒰.f i) (𝒰.f j) z) ∈ V j := by
        have : (V j).ι (pullback.snd (𝒰.f i) (𝒰.f j) z) ∈ Set.range (V j).ι := ⟨_, rfl⟩
        rwa [Scheme.Opens.range_ι] at this
      rw [hz] at h1
      exact hdisj i j hij _ h1 h2
  let f0 : X.left ⟶ Y.left := 𝒰.glueMorphisms fi hf
  have hf0 : ∀ i, (V i).ι ≫ f0 = fi i := fun i => 𝒰.ι_glueMorphisms fi hf i
  have hw : f0 ≫ Y.hom = X.hom := by
    apply 𝒰.hom_ext
    intro i
    change (V i).ι ≫ f0 ≫ Y.hom = (V i).ι ≫ X.hom
    rw [← Category.assoc, hf0]
    simp only [fi, Category.assoc, pullback.condition]
    have e1 : (g i).left ≫ pullback.snd Y.hom (U i).ι = pullback.snd X.hom (U i).ι := Over.w (g i)
    rw [← Category.assoc ((g i).left), e1, ← pullback.condition, ← Category.assoc,
      pullbackRestrictIsoRestrict_inv_fst]
  refine ⟨Over.homMk f0 hw, fun i => ?_⟩
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · rw [pbmap_left_fst, Over.homMk_left, ← pullbackRestrictIsoRestrict_hom_ι, Category.assoc, hf0]
    simp only [fi, Iso.hom_inv_id_assoc]
  · rw [pbmap_left_snd]
    exact (Over.w (g i)).symm

/-- The bijection `(T ⟶ F) ≃ ∀ i, (P i T ⟶ P i F)`. -/
def Ψ (X Y : Over S) : (X ⟶ Y) ≃ ∀ i, ((Over.pullback (U i).ι).obj X ⟶ (Over.pullback (U i).ι).obj Y) :=
  Equiv.ofBijective (fun f i => (Over.pullback (U i).ι).map f)
    ⟨fun f g h => glue_ext U hcov f g (fun i => congrFun h i),
     fun g => let ⟨f, hf⟩ := glue_exists U hcov hdisj g; ⟨f, funext hf⟩⟩

variable (F : Over S) [∀ i, GrpObj ((Over.pullback (U i).ι).obj F)]

/-- The group `Hom(T, F)`, transported from `∏ᵢ Hom(P i T, P i F)`. -/
abbrev grpT (T : Over S) : Group (T ⟶ F) := (Ψ U hcov hdisj T F).group

theorem comp_mul_T {T T' : Over S} (h : T' ⟶ T) (f g : T ⟶ F) :
    h ≫ (letI := grpT U hcov hdisj F T; f * g) =
      (letI := grpT U hcov hdisj F T'; (h ≫ f) * (h ≫ g)) := by
  letI := grpT U hcov hdisj F T
  letI := grpT U hcov hdisj F T'
  apply (Ψ U hcov hdisj T' F).injective
  funext i
  have e1 : Ψ U hcov hdisj T' F (h ≫ f * g) i =
      (Over.pullback (U i).ι).map h ≫ Ψ U hcov hdisj T F (f * g) i := by
    simp [Ψ]
  rw [e1]
  change _ = (Ψ U hcov hdisj T' F) ((Ψ U hcov hdisj T' F).symm
    (Ψ U hcov hdisj T' F (h ≫ f) * Ψ U hcov hdisj T' F (h ≫ g))) i
  change _ ≫ (Ψ U hcov hdisj T F) ((Ψ U hcov hdisj T F).symm
    (Ψ U hcov hdisj T F f * Ψ U hcov hdisj T F g)) i = _
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, Pi.mul_apply, Pi.mul_apply, MonObj.comp_mul]
  simp [Ψ]

/-- The presheaf of groups `T ↦ Hom(T, F)`. -/
def homGrp : (Over S)ᵒᵖ ⥤ GrpCat.{0} where
  obj T := @GrpCat.of (T.unop ⟶ F) (grpT U hcov hdisj F T.unop)
  map {T T'} h := @GrpCat.ofHom (T.unop ⟶ F) (T'.unop ⟶ F) (grpT U hcov hdisj F T.unop)
    (grpT U hcov hdisj F T'.unop)
    { toFun := fun f => h.unop ≫ f
      map_one' := by
        letI := grpT U hcov hdisj F T.unop
        letI := grpT U hcov hdisj F T'.unop
        apply (Ψ U hcov hdisj T'.unop F).injective
        funext i
        change (Over.pullback (U i).ι).map (h.unop ≫ (Ψ U hcov hdisj T.unop F).symm 1) =
          (Ψ U hcov hdisj T'.unop F) ((Ψ U hcov hdisj T'.unop F).symm 1) i
        rw [Equiv.apply_symm_apply, Functor.map_comp]
        have : (Over.pullback (U i).ι).map ((Ψ U hcov hdisj T.unop F).symm 1) = 1 := by
          change (Ψ U hcov hdisj T.unop F) ((Ψ U hcov hdisj T.unop F).symm 1) i = 1
          rw [Equiv.apply_symm_apply]; rfl
        rw [this, Pi.one_apply, MonObj.comp_one]
      map_mul' := fun f g => comp_mul_T U hcov hdisj F h.unop f g }
  map_id T := by
    ext f
    exact Category.id_comp f
  map_comp {T T' T''} h h' := by
    ext f
    exact Category.assoc _ _ _

/-- `F` represents `homGrp ⋙ forget`. -/
def homGrpRep : (homGrp U hcov hdisj F ⋙ forget GrpCat).RepresentableBy F where
  homEquiv := Equiv.refl _
  homEquiv_comp _ _ := rfl

/-- **The glued group object.** -/
abbrev grpObj_of_pieces : GrpObj F :=
  GrpObj.ofRepresentableBy F (homGrp U hcov hdisj F) (homGrpRep U hcov hdisj F)

/-- The base changes of the glued identity are the given identities. -/
theorem pb_eta (i : ι) :
    letI := grpObj_of_pieces U hcov hdisj F
    (Over.pullback (U i).ι).map (η[F] : 𝟙_ (Over S) ⟶ F) =
      toUnit _ ≫ η[(Over.pullback (U i).ι).obj F] := by
  letI := grpT U hcov hdisj F (𝟙_ (Over S))
  change (Ψ U hcov hdisj _ F) ((Ψ U hcov hdisj _ F).symm 1) i = _
  rw [Equiv.apply_symm_apply]
  rfl

end Glue

/-! ## §2. The field from the connected form -/

open ZInQ.Contrib.MumfordRigidity in
/-- **The field `mumfordGroupLaw`, exactly**, from GIT Thm 6.14 over a connected base, by gluing over the (open)
connected components. -/
theorem mumfordGroupLaw_of_conn (hC : MumfordGroupLawConn) : MumfordGroupLaw := by
  intro S F e hS hP hSm hGC he hfib
  haveI := hS
  -- the cover by connected components
  let ι := ConnectedComponents S
  let rep : ι → S := fun c => c.out
  let U : ι → S.Opens := fun c =>
    ⟨connectedComponent (rep c), isOpen_connectedComponent_of_isLocallyNoetherian S (rep c)⟩
  have hrep : ∀ c : ι, (ConnectedComponents.mk (rep c) : ι) = c := fun c => Quotient.out_eq c
  have hcov : ∀ s : S, ∃ i, s ∈ U i := by
    intro s
    refine ⟨ConnectedComponents.mk s, ?_⟩
    show s ∈ connectedComponent (rep (ConnectedComponents.mk s))
    have : connectedComponent (rep (ConnectedComponents.mk s)) = connectedComponent s :=
      ConnectedComponents.coe_eq_coe.mp (hrep _)
    rw [this]; exact mem_connectedComponent
  have hdisj : ∀ i j, i ≠ j → ∀ s : S, s ∈ U i → s ∉ U j := by
    intro i j hij s hi hj
    apply hij
    rw [← hrep i, ← hrep j]
    apply ConnectedComponents.coe_eq_coe.mpr
    change s ∈ connectedComponent (rep i) at hi
    change s ∈ connectedComponent (rep j) at hj
    rw [← connectedComponent_eq hi, ← connectedComponent_eq hj]
  -- the leaf on each component
  have piece : ∀ i, ∃ _G : GrpObj ((Over.pullback (U i).ι).obj F),
      η[(Over.pullback (U i).ι).obj F].left =
        pullback.lift ((U i).ι ≫ e) (𝟙 _) (by rw [Category.assoc, he, Category.id_comp, Category.comp_id]) := by
    intro i
    let Fi := (Over.pullback (U i).ι).obj F
    let ei : (U i).toScheme ⟶ Fi.left :=
      pullback.lift ((U i).ι ≫ e) (𝟙 _) (by rw [Category.assoc, he, Category.id_comp, Category.comp_id])
    haveI : IsProper F.hom := hP
    haveI : Smooth F.hom := hSm
    haveI : GeometricallyConnected F.hom := hGC
    have hconn : ConnectedSpace (U i).toScheme := by
      have : IsConnected (connectedComponent (rep i)) := isConnected_connectedComponent
      exact Subtype.connectedSpace this
    refine hC (U i).toScheme Fi ei inferInstance hconn
      (by change IsProper (pullback.snd F.hom (U i).ι); infer_instance)
      (by change Smooth (pullback.snd F.hom (U i).ι); infer_instance)
      (by change GeometricallyConnected (pullback.snd F.hom (U i).ι); infer_instance)
      (pullback.lift_snd _ _ _) ?_
    intro K _ s
    obtain ⟨A, g, hpb, hone⟩ := hfib K (s ≫ (U i).ι)
    have hw : g ≫ F.hom = (A.X.hom ≫ s) ≫ (U i).ι := by rw [hpb.w, Category.assoc]
    refine ⟨A, pullback.lift g (A.X.hom ≫ s) hw, ?_, ?_⟩
    · refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback F.hom (U i).ι)
      rw [pullback.lift_fst]
      exact hpb
    · apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, hone, Category.assoc, Category.assoc]
        change s ≫ (U i).ι ≫ e = s ≫ ei ≫ pullback.fst F.hom (U i).ι
        rw [pullback.lift_fst]
      · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, Category.assoc s, pullback.lift_snd,
          Category.comp_id]
        have h1 : (1 : A.Pt K).left ≫ A.X.hom = 𝟙 _ := Over.w (1 : A.Pt K)
        rw [h1, Category.id_comp]
  choose G hG using piece
  letI : ∀ i, GrpObj ((Over.pullback (U i).ι).obj F) := G
  letI := grpObj_of_pieces U hcov hdisj F
  refine ⟨inferInstance, ?_⟩
  have he' : e ≫ F.hom = (𝟙_ (Over S)).hom := he
  have key : (η[F] : 𝟙_ (Over S) ⟶ F) = Over.homMk e he' := by
    apply glue_ext U hcov
    intro i
    rw [pb_eta]
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · rw [Over.comp_left, Category.assoc, hG i, pullback.lift_fst, pbmap_left_fst, Over.homMk_left]
      have h1 : (toUnit ((Over.pullback (U i).ι).obj (𝟙_ (Over S)))).left ≫ 𝟙 _ =
          pullback.snd (𝟙_ (Over S)).hom (U i).ι := Over.w _
      rw [Category.comp_id] at h1
      rw [← Category.assoc, h1, ← pullback.condition_assoc]
      rfl
    · rw [Over.comp_left, Category.assoc, hG i, pullback.lift_snd, Category.comp_id, pbmap_left_snd]
      have h1 : (toUnit ((Over.pullback (U i).ι).obj (𝟙_ (Over S)))).left ≫ 𝟙 _ =
          pullback.snd (𝟙_ (Over S)).hom (U i).ι := Over.w _
      rw [Category.comp_id] at h1
      exact h1
  rw [key]
  rfl

end DictModels.MumfordConn

end

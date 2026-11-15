import ZInQKernel.OneProof.H.TailZ14

/-! Scratch test: a group structure on an open subscheme closed under the group law. -/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace CToPrinted.OpenSub

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] (W : G.left.Opens)

/-- Closure of an open set under the group law of `G`. -/
structure IsSubgroupOpen : Prop where
  one : ∀ s, (η[G] : 𝟙_ (Over S) ⟶ G).left s ∈ W
  mul : ∀ z : (G ⊗ G).left, (fst G G).left z ∈ W → (snd G G).left z ∈ W → (μ[G]).left z ∈ W
  inv : ∀ x : G.left, x ∈ W → (GrpObj.inv : G ⟶ G).left x ∈ W

variable {G W}

theorem mem_of_range {T : Over S} {f : T ⟶ G} (h : Set.range f.left ⊆ W) (t : T.left) :
    f.left t ∈ W := h ⟨t, rfl⟩

/-- The maps `T ⟶ G` landing in `W`, a subgroup. -/
def subHom (hW : IsSubgroupOpen G W) (T : Over S) : Subgroup (T ⟶ G) where
  carrier := {f | Set.range f.left ⊆ W}
  one_mem' := by
    rintro _ ⟨t, rfl⟩
    rw [Hom.one_def, Over.comp_left, Scheme.Hom.comp_apply]
    exact hW.one _
  mul_mem' := by
    intro f g hf hg
    rintro _ ⟨t, rfl⟩
    simp only [Set.mem_ofPred_eq] at hf hg
    rw [Hom.mul_def, Over.comp_left, Scheme.Hom.comp_apply]
    refine hW.mul _ ?_ ?_
    · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, lift_fst]
      exact mem_of_range hf t
    · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, lift_snd]
      exact mem_of_range hg t
  inv_mem' := by
    intro f hf
    rintro _ ⟨t, rfl⟩
    simp only [Set.mem_ofPred_eq] at hf
    rw [Hom.inv_def, Over.comp_left, Scheme.Hom.comp_apply]
    exact hW.inv _ (mem_of_range hf t)

/-- Precomposition, as a group homomorphism. -/
def subHomMap (hW : IsSubgroupOpen G W) {T T' : Over S} (h : T' ⟶ T) :
    subHom hW T →* subHom hW T' where
  toFun f := ⟨h ≫ f.1, by
    rintro _ ⟨t, rfl⟩
    rw [Over.comp_left, Scheme.Hom.comp_apply]
    exact mem_of_range f.2 _⟩
  map_one' := by
    apply Subtype.ext
    simp [Hom.one_def]
  map_mul' f g := by
    apply Subtype.ext
    simp [MonObj.comp_mul]

/-- The presheaf of groups `T ↦ {f : T ⟶ G | f(T) ⊆ W}`. -/
noncomputable def subFunctor (hW : IsSubgroupOpen G W) : (Over S)ᵒᵖ ⥤ GrpCat.{0} where
  obj T := GrpCat.of (subHom hW T.unop)
  map h := GrpCat.ofHom (subHomMap hW h.unop)
  map_id T := by
    ext f
    simp [subHomMap]
  map_comp h h' := by
    ext f
    simp [subHomMap]

variable (W) in
/-- The open subscheme on `W`, over `S`. -/
noncomputable abbrev G0 : Over S := Over.mk (W.ι ≫ G.hom)

variable (W) in
/-- Its inclusion into `G`. -/
noncomputable abbrev incl : G0 W ⟶ G := Over.homMk W.ι rfl

/-- Maps into `G0` are maps into `G` landing in `W`. -/
noncomputable def reprBy (hW : IsSubgroupOpen G W) :
    (subFunctor hW ⋙ forget GrpCat).RepresentableBy (G0 W) where
  homEquiv {T} :=
    { toFun := fun f => (⟨f ≫ incl W, by
        rintro _ ⟨t, rfl⟩
        rw [Over.comp_left, Scheme.Hom.comp_apply]
        have hm : W.ι (f.left t) ∈ Set.range W.ι := ⟨_, rfl⟩
        rw [Scheme.Opens.range_ι] at hm
        exact hm⟩ : subHom hW T)
      invFun := fun g => Over.homMk (IsOpenImmersion.lift W.ι g.1.left (by
          rw [Scheme.Opens.range_ι]; exact g.2)) (by
          simp only [G0, Over.mk_hom]
          rw [← Category.assoc, IsOpenImmersion.lift_fac, Over.w])
      left_inv := fun f => by
        apply Over.OverMorphism.ext
        simp only [Over.homMk_left]
        rw [← cancel_mono W.ι, IsOpenImmersion.lift_fac]
        rfl
      right_inv := fun g => by
        apply Subtype.ext
        apply Over.OverMorphism.ext
        simp only [Over.comp_left, Over.homMk_left]
        exact IsOpenImmersion.lift_fac _ _ _ }
  homEquiv_comp f g := Subtype.ext (Category.assoc f g (incl W))

/-- The group structure on `G0 W` (from `GrpObj.ofRepresentableBy`). -/
@[instance_reducible] noncomputable def grpG0 (hW : IsSubgroupOpen G W) : GrpObj (G0 W) :=
  GrpObj.ofRepresentableBy (G0 W) (subFunctor hW) (reprBy hW)

/-- The inclusion `G0 W → G` is a homomorphism. -/
theorem isMonHom_incl (hW : IsSubgroupOpen G W) :
    letI := grpG0 hW
    IsMonHom (incl W) := by
  letI := grpG0 hW
  constructor
  · have h1 : η[G0 W] ≫ incl W = ((reprBy hW).homEquiv η[G0 W]).1 := rfl
    have h2 : η[G0 W] = (reprBy hW).homEquiv.symm 1 := rfl
    rw [h1, h2, Equiv.apply_symm_apply]
    show (1 : 𝟙_ (Over S) ⟶ G) = η[G]
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  · have h1 : μ[G0 W] ≫ incl W = ((reprBy hW).homEquiv μ[G0 W]).1 := rfl
    have h2 : μ[G0 W] = (reprBy hW).homEquiv.symm
        ((reprBy hW).homEquiv (fst (G0 W) (G0 W)) * (reprBy hW).homEquiv (snd (G0 W) (G0 W))) := rfl
    rw [h1, h2, Equiv.apply_symm_apply]
    show ((fst (G0 W) (G0 W) ≫ incl W) * (snd (G0 W) (G0 W) ≫ incl W) : G0 W ⊗ G0 W ⟶ G) =
      (incl W ⊗ₘ incl W) ≫ μ[G]
    rw [Hom.mul_def]
    congr 1

end CToPrinted.OpenSub

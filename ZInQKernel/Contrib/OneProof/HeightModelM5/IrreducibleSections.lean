import Mathlib

/-!
# Sections of a sheaf on an irreducible space

Let `F` be a sheaf (valued in a concrete category such as abelian groups or modules) on a
topological space, and let `η` be a point specializing to every point of an open set `U`
(for instance the generic point of an irreducible space, with `U = ⊤`). If every stalk map
`F_s ⟶ F_η` along the specialization `η ⤳ s` (Mathlib's `stalkSpecializes`) is injective,
then the germ map `F(U) ⟶ F_η` is injective, and its image is the intersection over
`s ∈ U` of the images of the stalks `F_s`.

## Main statements

* `germ_injective_of_specializes`, `range_germ_eq_iInter_specializes`: the open-set form,
  for sheaves valued in a concrete category.
* `germ_top_injective_of_isGenericPoint`, `range_germ_top_eq_iInter_of_isGenericPoint`:
  global sections, with `η` a generic point.
* `modules_germ_generic_injective`, `modules_range_germ_generic`: the form for a sheaf of
  modules `M` on an irreducible scheme `S`, through `(Scheme.Modules.toPresheaf S).obj M`,
  with the image an intersection of additive subgroups of the generic stalk;
  `spec_modules_sections_generic` is the case `S = Spec R` with `R` a domain.
-/

universe w v u

open CategoryTheory Limits TopologicalSpace Opposite AlgebraicGeometry

namespace ZInQ.HeightModelM5

section General

variable {C : Type u} [Category.{v} C] {FC : C → C → Type w} {CC : C → Type v}
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{v} C FC]
  [HasColimits C] [HasLimits C] [PreservesLimits (forget C)]
  [PreservesFilteredColimits (forget C)] [(forget C).ReflectsIsomorphisms]
  {X : TopCat.{v}} (F : TopCat.Sheaf C X)

omit [HasLimits C] [PreservesLimits (forget C)] [PreservesFilteredColimits (forget C)]
  [(forget C).ReflectsIsomorphisms] in
/-- A section over `U` has the same image in `F_η` whether one takes its germ at `η`
directly or its germ at `s` followed by the stalk map along `η ⤳ s`. -/
theorem stalkSpecializes_germ_specializes {U : Opens X} {η s : X} (h : η ⤳ s) (hs : s ∈ U)
    (σ : ToType (F.presheaf.obj (op U))) :
    ConcreteCategory.hom (F.presheaf.stalkSpecializes h)
        (ConcreteCategory.hom (F.presheaf.germ U s hs) σ) =
      ConcreteCategory.hom (F.presheaf.germ U η (h.mem_open U.isOpen hs)) σ :=
  F.presheaf.germ_stalkSpecializes_apply hs h σ

/-- Injectivity of the germ map at `η`, when `η` specializes to every point of `U` and the
stalk maps `F_s ⟶ F_η` are injective. -/
theorem germ_injective_of_specializes {U : Opens X} {η : X} (hηU : η ∈ U)
    (hsp : ∀ s ∈ U, η ⤳ s)
    (hinj : ∀ (s : X) (hs : s ∈ U),
      Function.Injective (ConcreteCategory.hom (F.presheaf.stalkSpecializes (hsp s hs)))) :
    Function.Injective (ConcreteCategory.hom (F.presheaf.germ U η hηU)) := by
  intro σ τ h
  refine TopCat.Presheaf.section_ext F U σ τ fun s hs => hinj s hs ?_
  rw [stalkSpecializes_germ_specializes F (hsp s hs) hs σ,
    stalkSpecializes_germ_specializes F (hsp s hs) hs τ]
  exact h

/-- The image of the germ map at `η` is the intersection of the images of the stalk maps
`F_s ⟶ F_η`, `s ∈ U`. -/
theorem range_germ_eq_iInter_specializes {U : Opens X} {η : X} (hηU : η ∈ U)
    (hsp : ∀ s ∈ U, η ⤳ s)
    (hinj : ∀ (s : X) (hs : s ∈ U),
      Function.Injective (ConcreteCategory.hom (F.presheaf.stalkSpecializes (hsp s hs)))) :
    Set.range (ConcreteCategory.hom (F.presheaf.germ U η hηU)) =
      ⋂ (s : X) (hs : s ∈ U),
        Set.range (ConcreteCategory.hom (F.presheaf.stalkSpecializes (hsp s hs))) := by
  ext v
  simp only [Set.mem_iInter, Set.mem_range]
  constructor
  · rintro ⟨σ, rfl⟩ s hs
    exact ⟨_, stalkSpecializes_germ_specializes F (hsp s hs) hs σ⟩
  · intro hv
    choose w hw using hv
    have key : ∀ (s : X) (hs : s ∈ U), ∃ (W : Opens X) (hW : s ∈ W)
        (t : ToType (F.presheaf.obj (op W))),
        ConcreteCategory.hom (F.presheaf.germ W s hW) t = w s hs :=
      fun s hs => F.presheaf.exists_germ_eq (w s hs)
    choose W hW t ht using key
    let V : {s // s ∈ U} → Opens X := fun i => W i.1 i.2 ⊓ U
    let tV : ∀ i, ToType (F.presheaf.obj (op (V i))) := fun i =>
      ConcreteCategory.hom (F.presheaf.map (homOfLE inf_le_left : V i ⟶ W i.1 i.2).op)
        (t i.1 i.2)
    have hgermη : ∀ (i : {s // s ∈ U}) (hη : η ∈ W i.1 i.2),
        ConcreteCategory.hom (F.presheaf.germ (W i.1 i.2) η hη) (t i.1 i.2) = v := by
      intro i hη
      rw [← stalkSpecializes_germ_specializes F (hsp i.1 i.2) (hW i.1 i.2), ht, hw]
    have hgx : ∀ (i : {s // s ∈ U}) (x : X) (hx : x ∈ V i),
        ConcreteCategory.hom (F.presheaf.stalkSpecializes (hsp x hx.2))
          (ConcreteCategory.hom (F.presheaf.germ (V i) x hx) (tV i)) = v := by
      intro i x hx
      rw [stalkSpecializes_germ_specializes F (hsp x hx.2) hx (tV i)]
      simp only [tV, TopCat.Presheaf.germ_res_apply]
      exact hgermη i _
    have compat : TopCat.Presheaf.IsCompatible F.presheaf V tV := by
      intro i j
      refine TopCat.Presheaf.section_ext F (V i ⊓ V j) _ _ fun x hx => ?_
      have hxi : x ∈ V i := (inf_le_left : V i ⊓ V j ≤ V i) hx
      have hxj : x ∈ V j := (inf_le_right : V i ⊓ V j ≤ V j) hx
      have e1 := TopCat.Presheaf.germ_res_apply F.presheaf (Opens.infLELeft (V i) (V j)) x hx
        (tV i)
      have e2 := TopCat.Presheaf.germ_res_apply F.presheaf (Opens.infLERight (V i) (V j)) x hx
        (tV j)
      apply hinj x hxi.2
      rw [e1, e2, hgx i x hxi, hgx j x hxj]
    have hcov : U ≤ iSup V := fun x hx =>
      Opens.mem_iSup.2 ⟨⟨x, hx⟩, hW x hx, hx⟩
    obtain ⟨σ, hσ, -⟩ := F.existsUnique_gluing' V U
      (fun i => (homOfLE inf_le_right : V i ⟶ U)) hcov tV compat
    refine ⟨σ, ?_⟩
    let i₀ : {s // s ∈ U} := ⟨η, hηU⟩
    have hmem : η ∈ V i₀ := ⟨hW η hηU, hηU⟩
    rw [← TopCat.Presheaf.germ_res_apply F.presheaf (homOfLE inf_le_right : V i₀ ⟶ U) η hmem σ,
      hσ i₀]
    simp only [tV, TopCat.Presheaf.germ_res_apply]
    exact hgermη i₀ _

/-- Global sections inject into the stalk at a generic point, when the stalk maps
`F_s ⟶ F_η` are injective. -/
theorem germ_top_injective_of_isGenericPoint {η : X} (hη : IsGenericPoint η Set.univ)
    (hinj : ∀ s : X, Function.Injective (ConcreteCategory.hom
      (F.presheaf.stalkSpecializes (hη.specializes (Set.mem_univ s))))) :
    Function.Injective (ConcreteCategory.hom (F.presheaf.germ ⊤ η trivial)) :=
  germ_injective_of_specializes F (U := ⊤) trivial (fun s _ => hη.specializes (Set.mem_univ s))
    (fun s _ => hinj s)

/-- The image of the global sections in the stalk at a generic point is the intersection
of the images of all stalks. -/
theorem range_germ_top_eq_iInter_of_isGenericPoint {η : X} (hη : IsGenericPoint η Set.univ)
    (hinj : ∀ s : X, Function.Injective (ConcreteCategory.hom
      (F.presheaf.stalkSpecializes (hη.specializes (Set.mem_univ s))))) :
    Set.range (ConcreteCategory.hom (F.presheaf.germ ⊤ η trivial)) =
      ⋂ s : X, Set.range (ConcreteCategory.hom
        (F.presheaf.stalkSpecializes (hη.specializes (Set.mem_univ s)))) := by
  rw [range_germ_eq_iInter_specializes F (U := ⊤) trivial
    (fun s _ => hη.specializes (Set.mem_univ s)) (fun s _ => hinj s)]
  exact Set.iInter_congr fun s => iInf_pos trivial

end General

section Modules

variable {S : Scheme.{u}} [IrreducibleSpace S] (M : S.Modules)

/-- The underlying sheaf of abelian groups of a sheaf of modules on a scheme. -/
noncomputable def modulesAbSheaf : TopCat.Sheaf Ab.{u} S :=
  ⟨(Scheme.Modules.toPresheaf S).obj M, M.isSheaf⟩

/-- For a sheaf of modules on an irreducible scheme whose stalk maps to the generic stalk
are injective, global sections inject into the generic stalk. -/
theorem modules_germ_generic_injective
    (hinj : ∀ s : S, Function.Injective
      (((Scheme.Modules.toPresheaf S).obj M).stalkSpecializes
        ((genericPoint_spec S).specializes (Set.mem_univ s))).hom) :
    Function.Injective
      (((Scheme.Modules.toPresheaf S).obj M).germ ⊤ (genericPoint S) trivial).hom :=
  germ_top_injective_of_isGenericPoint (modulesAbSheaf M) (genericPoint_spec S) hinj

/-- For a sheaf of modules on an irreducible scheme whose stalk maps to the generic stalk
are injective, the image of the global sections in the generic stalk is the intersection of
the images of all stalks. -/
theorem modules_range_germ_generic
    (hinj : ∀ s : S, Function.Injective
      (((Scheme.Modules.toPresheaf S).obj M).stalkSpecializes
        ((genericPoint_spec S).specializes (Set.mem_univ s))).hom) :
    (((Scheme.Modules.toPresheaf S).obj M).germ ⊤ (genericPoint S) trivial).hom.range =
      ⨅ s : S, (((Scheme.Modules.toPresheaf S).obj M).stalkSpecializes
        ((genericPoint_spec S).specializes (Set.mem_univ s))).hom.range := by
  apply SetLike.coe_injective
  rw [AddMonoidHom.coe_range, AddSubgroup.coe_iInf]
  simp only [AddMonoidHom.coe_range]
  exact range_germ_top_eq_iInter_of_isGenericPoint (modulesAbSheaf M) (genericPoint_spec S)
    hinj

/-- The two statements together, for a sheaf of modules on `Spec R` with `R` a domain (the
case `R = 𝓞_L` of the application). -/
theorem spec_modules_sections_generic {R : CommRingCat.{u}} [IsDomain R]
    (M : (Spec R).Modules)
    (hinj : ∀ s : Spec R, Function.Injective
      (((Scheme.Modules.toPresheaf (Spec R)).obj M).stalkSpecializes
        ((genericPoint_spec (Spec R)).specializes (Set.mem_univ s))).hom) :
    Function.Injective
        (((Scheme.Modules.toPresheaf (Spec R)).obj M).germ ⊤ (genericPoint (Spec R))
          trivial).hom ∧
      (((Scheme.Modules.toPresheaf (Spec R)).obj M).germ ⊤ (genericPoint (Spec R))
          trivial).hom.range =
        ⨅ s : Spec R, (((Scheme.Modules.toPresheaf (Spec R)).obj M).stalkSpecializes
          ((genericPoint_spec (Spec R)).specializes (Set.mem_univ s))).hom.range :=
  ⟨modules_germ_generic_injective M hinj, modules_range_germ_generic M hinj⟩

end Modules

end ZInQ.HeightModelM5

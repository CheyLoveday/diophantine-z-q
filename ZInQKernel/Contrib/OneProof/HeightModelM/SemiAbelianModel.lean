import ZInQKernel.Contrib.OneProof.HeightModelM.OpenIdComp

/-!
# The semi-abelian model `𝒩⁰` of a semistable Néron model

GR1 (Gaudron–Rémond, Comment. Math. Helv. 89 (2014)), §2.3, p. 351, defines the height with
"`π : 𝒜 → Spec 𝒪_K` un modèle semi-abélien de `A`". `IsSemiAbelianModel` is that condition on
a group model (smooth, separated, quasi-compact, with generic fibre `A_K` as group schemes): at
every maximal ideal the special fibre is connected and is an extension of an abelian variety by a
torus, over `k(𝔭)` and over `k̄(𝔭)` (the two readings of `IsSemistablePrinted`, now for the whole
fibre).

`exists_semiAbelianModel`: if `𝒩⁰` is open (`OpenIdComp`), the open subscheme `𝒩⁰` of a group
model `𝒩` with semistable reduction as printed is a semi-abelian group model `𝒢₀`, with an open
immersion homomorphism `𝒢₀ → 𝒩` whose image is `𝒩⁰`. On each fibre the image is the identity
component (`SGA3Nbhd.idComp_baseChange'`, `ZInQ.SemiAbDescend.idCompSet_eq_cc`), so the printed
witness for `𝒩` becomes one for `𝒢₀` (`transfer_identityComponent`).
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits Topology MonObj
open MonoidalCategory CartesianMonoidalCategory CToPrinted
open DictModels.RaynaudOr ZInQ.DefFaltings ZInQ.HeightSplit ZInQ.HeightFix ZInQ.SemistabAssembly
open scoped NumberField

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace ZInQ.HeightModelM

/-! ## The predicate -/

section Pred

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L]
  [Algebra K L]

/-- **Semi-abelian group model** (GR1 §2.3, "modèle semi-abélien"; the fibres as in SGA 7 IX
Déf. 2.2, 3.1, locators UNVERIFIED): at every maximal ideal `𝔭` of `𝓞_L` the special fibre
`𝒜 ×_{𝓞_L} k(𝔭)` is connected and an extension of an abelian variety by a torus (split over
`k̄(𝔭)`), and so is the geometric fibre `𝒜 ×_{𝓞_L} k̄(𝔭)`. -/
def IsSemiAbelianModel (𝒜 : GroupModel A L) : Prop :=
  ∀ (𝔭 : Ideal (𝓞 L)) [𝔭.IsMaximal],
    (ConnectedSpace (resFibre 𝒜 𝔭).left ∧ HasSemiAbelianG0Torus (resFibre 𝒜 𝔭)) ∧
    (ConnectedSpace (geomFibre 𝒜 𝔭).left ∧ HasSemiAbelianG0 (geomFibre 𝒜 𝔭))

/-- A semi-abelian group model has semistable reduction as printed. -/
theorem IsSemiAbelianModel.isSemistablePrinted {𝒜 : GroupModel A L}
    (h : IsSemiAbelianModel 𝒜) : IsSemistablePrinted 𝒜 :=
  ⟨fun 𝔭 _ => (h 𝔭).2.2, fun 𝔭 _ => (h 𝔭).1.2⟩

end Pred

/-! ## Transfer along an open immersion onto the identity component -/

section Transfer

variable {k : Type} [Field k] {H X : Over (Spec (CommRingCat.of k))} [GrpObj H] [GrpObj X]

/-- If `j : H → X` is an open immersion homomorphism onto the identity component of `X`, then
`H` is connected, and an open subgroup `U` of `X` onto the identity component is also an open
subgroup of `H` onto the identity component of `H`. -/
theorem transfer_identityComponent (j : H ⟶ X) [IsOpenImmersion j.left] [IsMonHom j]
    (hj : Set.range j.left = connectedComponent (unitPt X))
    {U : Over (Spec (CommRingCat.of k))} [GrpObj U] (inc : U ⟶ X) [IsOpenImmersion inc.left]
    [IsMonHom inc] (hr : Set.range inc.left = connectedComponent (unitPt X)) :
    ConnectedSpace H.left ∧ ∃ inc' : U ⟶ H, IsOpenImmersion inc'.left ∧ IsMonHom inc' ∧
      Set.range inc'.left = connectedComponent (unitPt H) := by
  have hEq : Set.range inc.left = Set.range j.left := hr.trans hj.symm
  let e₀ := IsOpenImmersion.isoOfRangeEq inc.left j.left hEq
  have he₀ : e₀.hom ≫ j.left = inc.left := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  let e : U ≅ H := Over.isoMk e₀ (by
    rw [← Over.w j, ← Category.assoc, he₀, Over.w])
  have hfac : e.hom ≫ j = inc := Over.OverMorphism.ext he₀
  haveI : Mono j :=
    ⟨fun f g h => Over.OverMorphism.ext ((cancel_mono j.left).mp
      (by simpa using congrArg CommaMorphism.left h))⟩
  haveI : IsMonHom (e.hom ≫ j) := by rw [hfac]; infer_instance
  have hem : IsMonHom e.hom := AVGlue.isMonHom_of_comp_mono e.hom j
  have hUc : ConnectedSpace U.left := by
    have hconn : _root_.IsConnected (Set.range inc.left) := by
      rw [hr]; exact isConnected_connectedComponent
    haveI := Subtype.connectedSpace hconn
    exact (inc.left.isOpenEmbedding.toIsEmbedding.toHomeomorph).connectedSpace_iff.mpr this
  have hHc : ConnectedSpace H.left := (Scheme.homeoOfIso e₀).connectedSpace_iff.mp hUc
  refine ⟨hHc, e.hom, ?_, hem, ?_⟩
  · show IsOpenImmersion e₀.hom
    infer_instance
  · have h1 : Set.range e.hom.left = Set.univ :=
      Set.range_eq_univ.mpr (Scheme.homeoOfIso e₀).surjective
    rw [h1, PreconnectedSpace.connectedComponent_eq_univ]

/-- Transfer of the geometric printed form. -/
theorem hasSemiAbelianG0_transfer (j : H ⟶ X) [IsOpenImmersion j.left] [IsMonHom j]
    (hj : Set.range j.left = connectedComponent (unitPt X)) (h : HasSemiAbelianG0 X) :
    ConnectedSpace H.left ∧ HasSemiAbelianG0 H := by
  obtain ⟨U, hU, inc, hoi, hmh, hr, rest⟩ := h
  haveI := hoi
  haveI := hmh
  obtain ⟨hc, inc', h1, h2, h3⟩ := transfer_identityComponent j hj inc hr
  exact ⟨hc, U, hU, inc', h1, h2, h3, rest⟩

/-- Transfer of the `k(𝔭)` printed form. -/
theorem hasSemiAbelianG0Torus_transfer (j : H ⟶ X) [IsOpenImmersion j.left] [IsMonHom j]
    (hj : Set.range j.left = connectedComponent (unitPt X)) (h : HasSemiAbelianG0Torus X) :
    ConnectedSpace H.left ∧ HasSemiAbelianG0Torus H := by
  obtain ⟨U, hU, inc, hoi, hmh, hr, rest⟩ := h
  haveI := hoi
  haveI := hmh
  obtain ⟨hc, inc', h1, h2, h3⟩ := transfer_identityComponent j hj inc hr
  exact ⟨hc, U, hU, inc', h1, h2, h3, rest⟩

end Transfer

/-! ## The fibres of `𝒩⁰` -/

section Fibres

/-- The image of a base-changed morphism is the preimage of the image. -/
theorem range_pullback_map {S T : Scheme.{0}} (s : T ⟶ S) {X Y : Over S} (i : X ⟶ Y) :
    Set.range ((Over.pullback s).map i).left = pullback.fst Y.hom s ⁻¹' Set.range i.left := by
  have hm : ((Over.pullback s).map i).left =
      pullback.map X.hom s Y.hom s i.left (𝟙 _) (𝟙 _) (by simp) (by simp) := by
    apply pullback.hom_ext <;> simp [Over.pullback_map_left]
  rw [hm, Scheme.Pullback.range_map]
  have h : Set.range ((𝟙 T : T ⟶ T) : T → T) = Set.univ :=
    Set.range_eq_univ.mpr fun x => ⟨x, rfl⟩
  rw [h, Set.preimage_univ, Set.inter_univ]

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L]
  [Algebra K L]

/-- Over a field point `d : Spec k → Spec 𝓞_L`, the base change of an open immersion
homomorphism onto `𝒩⁰` is an open immersion homomorphism onto the identity component. -/
theorem range_fibre_map {k : Type} [Field k]
    (d : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (𝓞 L)))
    (𝒢₀ 𝒩 : GroupModel A L) (i : 𝒢₀.G ⟶ 𝒩.G) (hO : IsOpen (idCompSet 𝒩.G))
    (hr : Set.range i.left = idCompSet 𝒩.G) :
    letI : GrpObj ((Over.pullback d).obj 𝒩.G) := Functor.grpObjObj
    Set.range ((Over.pullback d).map i).left =
      connectedComponent (unitPt ((Over.pullback d).obj 𝒩.G)) := by
  letI : GrpObj ((Over.pullback d).obj 𝒩.G) := Functor.grpObjObj
  rw [range_pullback_map, hr,
    SGA3Nbhd.idComp_baseChange' geomConnOfRationalPoint_proof d 𝒩.G hO,
    ZInQ.SemiAbDescend.idCompSet_eq_cc ((Over.pullback d).obj 𝒩.G) default]

/-- **The fibres of `𝒩⁰` are semi-abelian**: an open immersion homomorphism `𝒢₀ → 𝒩` onto an
open `𝒩⁰`, with `𝒩` semistable as printed, makes `𝒢₀` a semi-abelian model. -/
theorem isSemiAbelianModel_of_range (𝒢₀ 𝒩 : GroupModel A L) (i : 𝒢₀.G ⟶ 𝒩.G)
    [IsOpenImmersion i.left] [IsMonHom i] (hO : IsOpen (idCompSet 𝒩.G))
    (hr : Set.range i.left = idCompSet 𝒩.G) (hS : IsSemistablePrinted 𝒩) :
    IsSemiAbelianModel 𝒢₀ := by
  intro 𝔭 _
  constructor
  · let d := sResP (L := L) 𝔭
    letI : GrpObj ((Over.pullback d).obj 𝒢₀.G) := Functor.grpObjObj
    letI : GrpObj ((Over.pullback d).obj 𝒩.G) := Functor.grpObjObj
    haveI : IsOpenImmersion ((Over.pullback d).map i).left :=
      ZInQ.H5Glue.isOpenImmersion_pullback_map _ i
    haveI : IsMonHom ((Over.pullback d).map i) := inferInstance
    exact hasSemiAbelianG0Torus_transfer ((Over.pullback d).map i)
      (range_fibre_map d 𝒢₀ 𝒩 i hO hr) (hS.2 𝔭)
  · let d := Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (ResBar 𝔭)))
    letI : GrpObj ((Over.pullback d).obj 𝒢₀.G) := Functor.grpObjObj
    letI : GrpObj ((Over.pullback d).obj 𝒩.G) := Functor.grpObjObj
    haveI : IsOpenImmersion ((Over.pullback d).map i).left :=
      ZInQ.H5Glue.isOpenImmersion_pullback_map _ i
    haveI : IsMonHom ((Over.pullback d).map i) := inferInstance
    exact hasSemiAbelianG0_transfer ((Over.pullback d).map i)
      (range_fibre_map d 𝒢₀ 𝒩 i hO hr) (hS.1 𝔭)

/-- **`𝒩⁰` is a semi-abelian group model** (given that `𝒩⁰` is open): a group model `𝒢₀` with an
open immersion homomorphism `𝒢₀ → 𝒩` with image `𝒩⁰`, semi-abelian when `𝒩` is semistable as
printed. -/
theorem exists_semiAbelianModel (𝒩 : GroupModel A L) (hO : IsOpen (idCompSet 𝒩.G))
    (hS : IsSemistablePrinted 𝒩) :
    ∃ (𝒢₀ : GroupModel A L) (i : 𝒢₀.G ⟶ 𝒩.G), IsOpenImmersion i.left ∧ IsMonHom i ∧
      Set.range i.left = idCompSet 𝒩.G ∧ IsSemiAbelianModel 𝒢₀ := by
  let W : 𝒩.G.left.Opens := ⟨idCompSet 𝒩.G, hO⟩
  have gc := SGA3Nbhd.idCompSubgroup_proof geomConnOfRationalPoint_proof _ 𝒩.G
  have hW : OpenSub.IsSubgroupOpen 𝒩.G W :=
    { one := fun s => idCompSet_one 𝒩.G s
      mul := gc.1
      inv := gc.2 }
  obtain ⟨𝒢₀, i, hoi, hmh, hr⟩ :=
    SGA3Nbhd.openSubgroupModel_at 𝒩 W hW (fun x hx => idCompGenericFibre K A L 𝒩 x hx)
  haveI := hoi
  haveI := hmh
  exact ⟨𝒢₀, i, hoi, hmh, hr, isSemiAbelianModel_of_range 𝒢₀ 𝒩 i hO hr hS⟩

end Fibres

end ZInQ.HeightModelM

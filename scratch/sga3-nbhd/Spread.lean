import ZInQKernel.Contrib.OneProof.SGA3NbhdOL
import ZInQKernel.Contrib.OneProof.EGAOpenImm
import ZInQKernel.Contrib.SpreadOut.NumberField

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField Topology
open MonoidalCategory CartesianMonoidalCategory MonObj CToPrinted

namespace SGA3Nbhd

/-- Open immersions of `Over`-pullback maps along a composite. -/
theorem openImm_pb_comp {X' Y' Z' : Scheme.{0}} (a : X' ⟶ Y') (b : Y' ⟶ Z') {P Q : Over Z'} (f : P ⟶ Q) :
    IsOpenImmersion ((Over.pullback (a ≫ b)).map f).left ↔
      IsOpenImmersion ((Over.pullback a).map ((Over.pullback b).map f)).left := by
  let e := Over.pullbackComp a b
  have hw := e.hom.naturality f
  refine MorphismProperty.arrow_mk_iso_iff @IsOpenImmersion
    (Arrow.isoMk ((Over.forget _).mapIso (e.app P)) ((Over.forget _).mapIso (e.app Q)) ?_)
  simp only [Functor.mapIso_hom, Iso.app_hom, Over.forget_map, Arrow.mk_hom]
  exact congrArg CommaMorphism.left hw.symm

theorem openImm_pb_congr {X' Z' : Scheme.{0}} {a a' : X' ⟶ Z'} (h : a = a') {P Q : Over Z'} (f : P ⟶ Q) :
    IsOpenImmersion ((Over.pullback a).map f).left ↔ IsOpenImmersion ((Over.pullback a').map f).left := by
  subst h; rfl

open ZInQ.Contrib.SpreadOut.NF ReductGlue in
/-- **Spreading out an open immersion from the generic fibre** (EGA IV₃ 8.10.5, the open-immersion item,
proved in the tree as `egaIV_8_10_5_openImm_proof`, for `Spec L = lim Spec 𝓞_L[1/n!]`): a morphism of smooth,
separated, quasi-compact `𝓞_L`-schemes whose generic fibre is an isomorphism is an open immersion over every
DVR `O` of `L` in which `n!` is a unit, for some `n`. -/
theorem spread_openImm {L : Type} [Field L] [NumberField L] (X Y : Over (Spec (CommRingCat.of (𝓞 L))))
    [Smooth X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [Smooth Y.hom] [QuasiCompact Y.hom]
    [IsSeparated Y.hom] (f : X ⟶ Y)
    (hf : IsIso ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L)))).map f)) :
    ∃ n : ℕ, ∀ (O : ValuationSubring L) [IsDiscreteValuationRing O], IsUnit (toOL O (sf L n)) →
      IsOpenImmersion ((Over.pullback (gO O)).map f).left := by
  let g0 : (specDiag L).obj (Opposite.op 0) ⟶ Spec (CommRingCat.of (𝓞 L)) :=
    Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (Rg L 0)))
  let Xi : Over ((specDiag L).obj (Opposite.op 0)) := (Over.pullback g0).obj X
  let Yi : Over ((specDiag L).obj (Opposite.op 0)) := (Over.pullback g0).obj Y
  let fi : Xi ⟶ Yi := (Over.pullback g0).map f
  have hX1 : LocallyOfFinitePresentation Xi.hom :=
    show LocallyOfFinitePresentation (pullback.snd X.hom g0) from inferInstance
  have hX2 : QuasiCompact Xi.hom := show QuasiCompact (pullback.snd X.hom g0) from inferInstance
  have hX3 : QuasiSeparated Xi.hom := show QuasiSeparated (pullback.snd X.hom g0) from inferInstance
  have hY1 : LocallyOfFinitePresentation Yi.hom :=
    show LocallyOfFinitePresentation (pullback.snd Y.hom g0) from inferInstance
  have hY2 : QuasiCompact Yi.hom := show QuasiCompact (pullback.snd Y.hom g0) from inferInstance
  have hY3 : QuasiSeparated Yi.hom := show QuasiSeparated (pullback.snd Y.hom g0) from inferInstance
  have hc0 : (specCone L).π.app (Opposite.op 0) ≫ g0 =
      Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L)) := by
    show Spec.map (CommRingCat.ofHom (toL L 0)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (Rg L 0))) = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    exact toL_alg L 0 x
  have hlim : IsOpenImmersion ((Over.pullback ((specCone L).π.app (Opposite.op 0))).map fi).left := by
    rw [← openImm_pb_comp, openImm_pb_congr hc0]
    haveI := hf
    change IsOpenImmersion ((Over.forget _).map
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L)))).map f))
    infer_instance
  obtain ⟨j, a, hj⟩ := ZInQ.Contrib.EGAOpenImm.egaIV_8_10_5_openImm_proof ℕ (specDiag L) (specCone L)
    (specConeIsLimit L) (Opposite.op 0) Xi Yi hX1 hX2 hX3 hY1 hY2 hY3 fi hlim
  refine ⟨j.unop, fun O _ hu => ?_⟩
  let ℓ : Rg L j.unop →+* O := IsLocalization.Away.lift (sf L j.unop) hu
  have heq : gO O = Spec.map (CommRingCat.ofHom ℓ) ≫ ((specDiag L).map a ≫ g0) := by
    show Spec.map _ = Spec.map _ ≫ (Spec.map _ ≫ Spec.map _)
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [tr_alg]
    exact congrArg Subtype.val (IsLocalization.Away.lift_eq (sf L j.unop) hu x).symm
  haveI := hj
  have h1 : IsOpenImmersion ((Over.pullback (Spec.map (CommRingCat.ofHom ℓ))).map
      ((Over.pullback ((specDiag L).map a)).map fi)).left :=
    ZInQ.H5Glue.isOpenImmersion_pullback_map _ _
  have heq' : gO O = (Spec.map (CommRingCat.ofHom ℓ) ≫ (specDiag L).map a) ≫ g0 := by
    rw [heq]; exact (Category.assoc _ _ _).symm
  exact (openImm_pb_congr heq' f).mpr ((openImm_pb_comp _ g0 f).mpr
    ((openImm_pb_comp (Spec.map (CommRingCat.ofHom ℓ)) ((specDiag L).map a) fi).mpr h1))


open MonoidalCategory CartesianMonoidalCategory MonObj CToPrinted in
/-- The points of `G ×_S S'` over `s'` whose image lies in an open `V ⊆ G` form a preconnected set, if
`V ×_S Spec κ(s')` is connected (the argument of `CToPrinted.idComp_baseChange`, for one point). -/
theorem preconnected_P {S S' : Scheme.{0}} (g : S' ⟶ S) (G : Over S) (W : G.left.Opens) (s' : S')
    (hc : ConnectedSpace ↥(pullback (W.ι ≫ G.hom) ((S').fromSpecResidueField s' ≫ g))) :
    _root_.IsPreconnected
      {w : ((Over.pullback g).obj G).left | pullback.fst G.hom g w ∈ W ∧ pullback.snd G.hom g w = s'} := by
  let f0 := W.ι ≫ G.hom
  let m2 := pullback.map f0 g G.hom g W.ι (𝟙 _) (𝟙 _) (by simp [f0]) (by simp)
  let r := (S').fromSpecResidueField s'
  let m1 := pullback.fst (pullback.snd f0 g) r
  haveI : ConnectedSpace ↥(pullback (pullback.snd f0 g) r) :=
    (Scheme.homeoOfIso (pullbackLeftPullbackSndIso f0 g r)).connectedSpace_iff.mpr hc
  have hrange : Set.range (m1 ≫ m2) =
      {w : ((Over.pullback g).obj G).left | pullback.fst G.hom g w ∈ W ∧ pullback.snd G.hom g w = s'} := by
    ext w
    constructor
    · rintro ⟨u, rfl⟩
      constructor
      · rw [← Scheme.Hom.comp_apply, Category.assoc, pullback.lift_fst, ← Category.assoc,
          Scheme.Hom.comp_apply]
        have : W.ι ((m1 ≫ pullback.fst f0 g) u) ∈ Set.range W.ι := ⟨_, rfl⟩
        rwa [Scheme.Opens.range_ι] at this
      · rw [← Scheme.Hom.comp_apply, Category.assoc, pullback.lift_snd, Category.comp_id,
          pullback.condition, Scheme.Hom.comp_apply]
        have : r (pullback.snd (pullback.snd f0 g) r u) ∈ Set.range r := ⟨_, rfl⟩
        rwa [Scheme.range_fromSpecResidueField] at this
    · rintro ⟨h1, h2⟩
      have hw : w ∈ Set.range m2 := by
        rw [Scheme.Pullback.range_map]
        refine ⟨?_, ⟨pullback.snd G.hom g w, rfl⟩⟩
        show pullback.fst G.hom g w ∈ Set.range W.ι
        rw [Scheme.Opens.range_ι]
        exact h1
      obtain ⟨v, rfl⟩ := hw
      have hv : pullback.snd f0 g v ∈ Set.range r := by
        rw [Scheme.range_fromSpecResidueField]
        have : (m2 ≫ pullback.snd G.hom g) v = s' := h2
        rw [pullback.lift_snd, Category.comp_id] at this
        exact this
      have hv' : v ∈ Set.range m1 := by
        rw [Scheme.Pullback.range_fst]
        exact hv
      obtain ⟨u, rfl⟩ := hv'
      exact ⟨u, rfl⟩
  rw [← hrange]
  exact (isConnected_range (m1 ≫ m2).continuous).isPreconnected

open MonoidalCategory CartesianMonoidalCategory MonObj CToPrinted in
/-- **One fibre of `V → S` is geometrically connected** when `V ∩ G_s = (G_s)⁰` and `V` contains the unit
section (Stacks 04KV, the bundle leaf `GeomConnOfRationalPoint`); hence its base change to any field over
`κ(s)` is connected. -/
theorem connected_fibre_V (hG : AVGlue.GeomConnOfRationalPoint) {S : Scheme.{0}} (G : Over S) [GrpObj G]
    (W : G.left.Opens) [LocallyOfFiniteType (W.ι ≫ G.hom)] [QuasiCompact (W.ι ≫ G.hom)] (y : S)
    (hV : ∀ x, (x ∈ W ∧ G.hom x = y) ↔
      x ∈ connectedComponentIn (G.hom ⁻¹' {y}) ((η[G] : 𝟙_ (Over S) ⟶ G).left y))
    (he : ∀ t, (η[G] : 𝟙_ (Over S) ⟶ G).left t ∈ W) {K : Type} [Field K]
    (φ : Spec (CommRingCat.of K) ⟶ Spec (S.residueField y)) :
    ConnectedSpace ↥(pullback (W.ι ≫ G.hom) (φ ≫ S.fromSpecResidueField y)) := by
  let f0 : W.toScheme ⟶ S := W.ι ≫ G.hom
  have hT : _root_.IsConnected (f0 ⁻¹' {y}) := by
    let C := connectedComponentIn (G.hom ⁻¹' {y}) ((η[G] : 𝟙_ (Over S) ⟶ G).left y)
    have hey : (η[G] : 𝟙_ (Over S) ⟶ G).left y ∈ G.hom ⁻¹' {y} := SGA3IdComp.hom_e G y
    have hC : _root_.IsConnected C := isConnected_connectedComponentIn_iff.mpr hey
    have himg : W.ι '' (f0 ⁻¹' {y}) = C := by
      ext x
      constructor
      · rintro ⟨w, hw, rfl⟩
        have hw' : G.hom (W.ι w) = y := hw
        have hmem : W.ι w ∈ W := by
          have : W.ι w ∈ Set.range W.ι := ⟨w, rfl⟩
          rwa [Scheme.Opens.range_ι] at this
        exact (hV _).mp ⟨hmem, hw'⟩
      · intro hx
        obtain ⟨hxW, hxy⟩ := (hV x).mpr hx
        have hxW' : x ∈ Set.range W.ι := by rw [Scheme.Opens.range_ι]; exact hxW
        obtain ⟨w, rfl⟩ := hxW'
        exact ⟨w, hxy, rfl⟩
    rw [← himg] at hC
    exact ⟨hC.1.of_image, (W.ι.isOpenEmbedding.isInducing.isPreconnected_image).mp hC.2⟩
  haveI : ConnectedSpace (f0 ⁻¹' {y}) := isConnected_iff_connectedSpace.mp hT
  haveI hconn : ConnectedSpace (f0.fiber y) := (f0.fiberHomeo y).connectedSpace_iff.mpr inferInstance
  have hη : Set.range (η[G] : 𝟙_ (Over S) ⟶ G).left ⊆ Set.range W.ι := by
    rintro _ ⟨s, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact he s
  let eW : S ⟶ W.toScheme := IsOpenImmersion.lift W.ι (η[G] : 𝟙_ (Over S) ⟶ G).left hη
  have heW : eW ≫ f0 = 𝟙 S := by
    show eW ≫ W.ι ≫ G.hom = 𝟙 S
    rw [← Category.assoc, IsOpenImmersion.lift_fac, Over.w]
    rfl
  let sec : Spec (S.residueField y) ⟶ f0.fiber y :=
    pullback.lift (S.fromSpecResidueField y ≫ eW) (𝟙 _) (by
      rw [Category.assoc, heW, Category.comp_id, Category.id_comp])
  have hsec : sec ≫ f0.fiberToSpecResidueField y = 𝟙 _ := pullback.lift_snd _ _ _
  have hgc : GeometricallyConnected (f0.fiberToSpecResidueField y) :=
    hG (S.residueField y) (f0.fiber y) (f0.fiberToSpecResidueField y) sec hsec
      (show LocallyOfFiniteType (pullback.snd f0 (S.fromSpecResidueField y)) from inferInstance)
      (show QuasiCompact (pullback.snd f0 (S.fromSpecResidueField y)) from inferInstance) hconn
  have hcs : ConnectedSpace ↥(pullback (f0.fiberToSpecResidueField y) φ) :=
    hgc.geometrically_connectedSpace φ (pullback.fst _ _) (pullback.snd _ _) (IsPullback.of_hasPullback _ _)
  exact (Scheme.homeoOfIso (pullbackLeftPullbackSndIso f0 (S.fromSpecResidueField y) φ).symm).connectedSpace_iff.mpr
    hcs

open MonoidalCategory CartesianMonoidalCategory MonObj CToPrinted in
/-- **SGA 3 VI_B 3.3 at one point, without openness of `G⁰`** (the hard inclusion): for `g : S' → S`, a point
`z` of `G ×_S S'` over `s'` with `g(s')` closed, if `pr₁ z ∈ G⁰` then `z ∈ (G ×_S S')⁰`. Uses the open
`V = G \ (G_s \ G_s⁰)` (`isClosed_fibre_diff`) in place of `G⁰`. -/
theorem mem_idCompSet_bc (hG : AVGlue.GeomConnOfRationalPoint) {S S' : Scheme.{0}} [IsNoetherian S]
    (g : S' ⟶ S) (G : Over S) [GrpObj G] [Smooth G.hom] [QuasiCompact G.hom]
    (z : ((Over.pullback g).obj G).left) (hs : IsClosed ({g (pullback.snd G.hom g z)} : Set S))
    (hz : pullback.fst G.hom g z ∈ idCompSet G) :
    letI : GrpObj ((Over.pullback g).obj G) := Functor.grpObjObj
    z ∈ idCompSet ((Over.pullback g).obj G) := by
  letI : GrpObj ((Over.pullback g).obj G) := Functor.grpObjObj
  set s' := pullback.snd G.hom g z with hs'
  set y := g s' with hy
  let C := connectedComponentIn (G.hom ⁻¹' {y}) ((η[G] : 𝟙_ (Over S) ⟶ G).left y)
  have hVc : IsClosed (G.hom ⁻¹' {y} \ C) := isClosed_fibre_diff G y hs
  let W : G.left.Opens := ⟨(G.hom ⁻¹' {y} \ C)ᶜ, hVc.isOpen_compl⟩
  haveI : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  haveI : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  haveI : IsNoetherian G.left := {}
  have hV : ∀ x, (x ∈ W ∧ G.hom x = y) ↔ x ∈ C := by
    intro x
    constructor
    · rintro ⟨hxW, hxy⟩
      by_contra hxC
      exact hxW ⟨hxy, hxC⟩
    · intro hx
      exact ⟨fun h => h.2 hx, connectedComponentIn_subset (G.hom ⁻¹' {y}) _ hx⟩
  have he : ∀ t, (η[G] : 𝟙_ (Over S) ⟶ G).left t ∈ W := by
    intro t ht
    obtain ⟨h1, h2⟩ := ht
    have h1' : t = y := by rw [← SGA3IdComp.hom_e G t]; exact h1
    subst h1'
    exact h2 (mem_connectedComponentIn (SGA3IdComp.hom_e G _))
  let e' := (η[(Over.pullback g).obj G] : 𝟙_ (Over S') ⟶ _).left
  let e := (η[G] : 𝟙_ (Over S) ⟶ G).left
  have hu1 : ∀ s', pullback.fst G.hom g (e' s') = e (g s') := by
    intro s'
    rw [← Scheme.Hom.comp_apply, unit_bc_fst g G, Scheme.Hom.comp_apply]
  have hu2 : ∀ s', pullback.snd G.hom g (e' s') = s' := by
    intro s'
    show ((Over.pullback g).obj G).hom (e' s') = s'
    rw [← Scheme.Hom.comp_apply, Over.w]
    rfl
  have hc : ConnectedSpace ↥(pullback (W.ι ≫ G.hom) ((S').fromSpecResidueField s' ≫ g)) := by
    rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    exact connected_fibre_V hG G W y hV he _
  have hP := preconnected_P g G W s' hc
  have hzC : pullback.fst G.hom g z ∈ C := by
    have h2 : pullback.fst G.hom g z ∈ connectedComponentIn
        (G.hom ⁻¹' {G.hom (pullback.fst G.hom g z)})
        ((η[G] : 𝟙_ (Over S) ⟶ G).left (G.hom (pullback.fst G.hom g z))) := hz
    have hfib : G.hom (pullback.fst G.hom g z) = y := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    rwa [hfib] at h2
  show z ∈ connectedComponentIn (((Over.pullback g).obj G).hom ⁻¹' {((Over.pullback g).obj G).hom z})
    (e' (((Over.pullback g).obj G).hom z))
  refine hP.subset_connectedComponentIn ⟨?_, hu2 s'⟩ ?_ ⟨(hV _).mpr hzC |>.1, rfl⟩
  · rw [hu1]
    exact he _
  · rintro w ⟨-, hw⟩
    exact hw

open MonoidalCategory CartesianMonoidalCategory MonObj CToPrinted in
/-- **SGA 3 VI_B 3.3, the easy inclusion** (any base change, no hypothesis): `pr₁` maps `(G ×_S S')⁰` into
`G⁰` (the second half of `CToPrinted.idComp_baseChange`). -/
theorem mem_idCompSet_of_bc {S S' : Scheme.{0}} (g : S' ⟶ S) (G : Over S) [GrpObj G]
    (z : ((Over.pullback g).obj G).left) :
    letI : GrpObj ((Over.pullback g).obj G) := Functor.grpObjObj
    z ∈ idCompSet ((Over.pullback g).obj G) → pullback.fst G.hom g z ∈ idCompSet G := by
  letI : GrpObj ((Over.pullback g).obj G) := Functor.grpObjObj
  intro hz
  let e' := (η[(Over.pullback g).obj G] : 𝟙_ (Over S') ⟶ _).left
  let e := (η[G] : 𝟙_ (Over S) ⟶ G).left
  have hu1 : ∀ s', pullback.fst G.hom g (e' s') = e (g s') := by
    intro s'
    rw [← Scheme.Hom.comp_apply, unit_bc_fst g G, Scheme.Hom.comp_apply]
  have hu2 : ∀ s', pullback.snd G.hom g (e' s') = s' := by
    intro s'
    show ((Over.pullback g).obj G).hom (e' s') = s'
    rw [← Scheme.Hom.comp_apply, Over.w]
    rfl
  have hfib : ∀ w : ((Over.pullback g).obj G).left, G.hom (pullback.fst G.hom g w) = g (pullback.snd G.hom g w) := by
    intro w
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  let s' := pullback.snd G.hom g z
  have hz' : z ∈ connectedComponentIn (pullback.snd G.hom g ⁻¹' {s'}) (e' s') := hz
  set C := connectedComponentIn (pullback.snd G.hom g ⁻¹' {s'}) (e' s')
  have hC : _root_.IsPreconnected (pullback.fst G.hom g '' C) :=
    isPreconnected_connectedComponentIn.image _ (pullback.fst G.hom g).continuous.continuousOn
  have hsub : pullback.fst G.hom g '' C ⊆ G.hom ⁻¹' {g s'} := by
    rintro _ ⟨w, hw, rfl⟩
    show G.hom (pullback.fst G.hom g w) = g s'
    rw [hfib]
    exact congrArg g (connectedComponentIn_subset (pullback.snd G.hom g ⁻¹' {s'}) _ hw)
  have hmem : e (g s') ∈ pullback.fst G.hom g '' C :=
    ⟨e' s', mem_connectedComponentIn (hu2 s'), hu1 s'⟩
  have := hC.subset_connectedComponentIn hmem hsub ⟨z, hz', rfl⟩
  show pullback.fst G.hom g z ∈ connectedComponentIn (G.hom ⁻¹' {G.hom (pullback.fst G.hom g z)})
    (e (G.hom (pullback.fst G.hom g z)))
  rw [hfib]
  exact this
/-- Over a DVR, a fibre over a non-closed point is preconnected if `pullback G.hom (Spec F → Spec R)` is. -/
theorem isPreconnected_fibre_dvr {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (G : Over (Spec (CommRingCat.of R))) {F : Type} [Field F] (φ : R →+* F) (hφ : Function.Injective φ)
    (hc : _root_.IsPreconnected
      (Set.univ : Set ↥(pullback (C := Scheme.{0}) G.hom (Spec.map (CommRingCat.ofHom φ)))))
    (t : Spec (CommRingCat.of R)) (ht : t ≠ IsLocalRing.closedPoint R) :
    _root_.IsPreconnected (G.hom ⁻¹' {t}) := by
  have ht0 : t.asIdeal = ⊥ := by
    by_contra h
    have hm : t.asIdeal.IsMaximal := Ring.DimensionLEOne.maximalOfPrime h t.isPrime
    exact ht (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hm))
  have hr : G.hom ⁻¹' {t} = Set.range (pullback.fst G.hom (Spec.map (CommRingCat.ofHom φ))) := by
    rw [Scheme.Pullback.range_fst]
    congr 1
    ext u
    simp only [Set.mem_singleton_iff, Set.mem_range]
    constructor
    · rintro rfl
      refine ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum F), ?_⟩
      apply PrimeSpectrum.ext
      rw [ht0]
      show Ideal.comap φ ⊥ = ⊥
      exact Ideal.comap_bot_of_injective _ hφ
    · rintro ⟨v, rfl⟩
      apply PrimeSpectrum.ext
      rw [ht0]
      have hv : v.asIdeal = ⊥ := (Ideal.eq_bot_or_top _).resolve_right v.isPrime.ne_top
      show Ideal.comap φ v.asIdeal = ⊥
      rw [hv]
      exact Ideal.comap_bot_of_injective _ hφ
  rw [hr, ← Set.image_univ]
  exact hc.image _ (pullback.fst G.hom (Spec.map (CommRingCat.ofHom φ))).continuous.continuousOn

open ReductSplit in
/-- In a group model over a DVR, every point over the generic point lies in `G⁰`. -/
theorem mem_idCompSet_groupModelO_generic {K : Type} [Field K] {A : PkgI3.AbVar K} {O : ValuationSubring K}
    [IsDiscreteValuationRing O] (𝒩 : GroupModelO A O) (z : 𝒩.G.left)
    (hz : 𝒩.G.hom z ≠ IsLocalRing.closedPoint O) : z ∈ idCompSet 𝒩.G := by
  have hc : _root_.IsPreconnected (Set.univ : Set ↥(pullback (C := Scheme.{0}) 𝒩.G.hom
      (Spec.map (CommRingCat.ofHom (algebraMap O K))))) := by
    haveI : IsIntegral A.X.left := GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom
    let e : pullback 𝒩.G.hom (Spec.map (CommRingCat.ofHom (algebraMap O K))) ≅ A.X.left :=
      (Over.forget _).mapIso 𝒩.gen
    have h1 : _root_.IsPreconnected (Set.univ : Set A.X.left) :=
      (IrreducibleSpace.isIrreducible_univ _).2.isPreconnected
    have h2 := h1.image _ (Scheme.homeoOfIso e.symm).continuous.continuousOn
    rwa [Set.image_univ_of_surjective (Scheme.homeoOfIso e.symm).surjective] at h2
  have hp := isPreconnected_fibre_dvr 𝒩.G (algebraMap O K) (FaithfulSMul.algebraMap_injective O K) hc _ hz
  show z ∈ connectedComponentIn (𝒩.G.hom ⁻¹' {𝒩.G.hom z}) ((η[𝒩.G] : 𝟙_ (Over _) ⟶ 𝒩.G).left (𝒩.G.hom z))
  exact hp.subset_connectedComponentIn (SGA3IdComp.hom_e 𝒩.G _) le_rfl rfl

open ZInQ.HeightSplit ZInQ.DefFaltings in
/-- **An open subgroup `W` of a group model over `𝓞_L` containing the generic fibre is a group model** (the
construction of `identityComponentOLRange_of` with `𝒢⁰` replaced by `W`); original doc: from the bundle leaf
`AVGlue.GeomConnOfRationalPoint` (the construction of `identityComponentGroupModel_of`). -/
theorem openSubgroupModel_at {K : Type} [Field K]
    {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L] (𝒢 : GroupModel A L)
    (W : 𝒢.G.left.Opens) (hW : OpenSub.IsSubgroupOpen 𝒢.G W)
    (hgen : ∀ x : 𝒢.G.left, (𝒢.G.hom x).asIdeal = ⊥ → x ∈ (W : Set 𝒢.G.left)) :
    ∃ (𝒢₀ : GroupModel A L) (i : 𝒢₀.G ⟶ 𝒢.G), IsOpenImmersion i.left ∧
      IsMonHom i ∧ Set.range i.left = (W : Set 𝒢.G.left) := by
  letI : GrpObj (OpenSub.G0 W) := OpenSub.grpG0 hW
  have hmon : IsMonHom (OpenSub.incl W) := OpenSub.isMonHom_incl hW
  haveI : Smooth (OpenSub.G0 W).hom := show Smooth (W.ι ≫ 𝒢.G.hom) from inferInstance
  haveI : IsSeparated (OpenSub.G0 W).hom := show IsSeparated (W.ι ≫ 𝒢.G.hom) from inferInstance
  haveI : QuasiCompact (OpenSub.G0 W).hom := by
    haveI : IsLocallyNoetherian 𝒢.G.left := LocallyOfFiniteType.isLocallyNoetherian 𝒢.G.hom
    haveI : CompactSpace 𝒢.G.left := QuasiCompact.compactSpace_of_compactSpace 𝒢.G.hom
    haveI : IsNoetherian 𝒢.G.left := {}
    show QuasiCompact (W.ι ≫ 𝒢.G.hom)
    infer_instance
  let jL := Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L))
  have hmap : ((Over.pullback jL).map (OpenSub.incl W)).left =
      pullback.map (W.ι ≫ 𝒢.G.hom) jL 𝒢.G.hom jL W.ι (𝟙 _) (𝟙 _) (by simp) (by simp) := by
    apply pullback.hom_ext <;> simp [Over.pullback_map_left]
  haveI : IsOpenImmersion (OpenSub.incl W).left := show IsOpenImmersion W.ι from inferInstance
  have hiso : IsIso ((Over.pullback jL).map (OpenSub.incl W)).left := by
    rw [isIso_iff_isOpenImmersion_and_surjective]
    refine ⟨ZInQ.H5Glue.isOpenImmersion_pullback_map _ _, ⟨fun z => ?_⟩⟩
    have hz : z ∈ Set.range ((Over.pullback jL).map (OpenSub.incl W)).left := by
      rw [hmap, Scheme.Pullback.range_map]
      refine ⟨?_, ⟨pullback.snd 𝒢.G.hom jL z, rfl⟩⟩
      show pullback.fst 𝒢.G.hom jL z ∈ Set.range W.ι
      rw [Scheme.Opens.range_ι]
      apply hgen
      have h1 : 𝒢.G.hom (pullback.fst 𝒢.G.hom jL z) = jL (pullback.snd 𝒢.G.hom jL z) := by
        rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
      rw [h1]
      set p := pullback.snd 𝒢.G.hom jL z
      have hp : p.asIdeal = ⊥ :=
        (Ideal.eq_bot_or_top p.asIdeal).resolve_right p.isPrime.ne_top
      show Ideal.comap (algebraMap (𝓞 L) L) p.asIdeal = ⊥
      rw [hp]
      exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 L) L)
    exact hz
  haveI : IsIso ((Over.forget _).map ((Over.pullback jL).map (OpenSub.incl W))) := hiso
  haveI : IsIso ((Over.pullback jL).map (OpenSub.incl W)) :=
    isIso_of_reflects_iso _ (Over.forget _)
  let e := asIso ((Over.pullback jL).map (OpenSub.incl W))
  haveI := hmon
  let 𝒢₀ : GroupModel A L :=
    { G := OpenSub.G0 W
      gen := e ≪≫ 𝒢.gen
      gen_hom := by
        letI : GrpObj (genericFibre L (OpenSub.G0 W)) := Functor.grpObjObj
        letI : GrpObj (genericFibre L 𝒢.G) := Functor.grpObjObj
        letI : GrpObj ((Over.pullback jL).obj (OpenSub.G0 W)) := Functor.grpObjObj
        letI : GrpObj ((Over.pullback jL).obj 𝒢.G) := Functor.grpObjObj
        have h1 : IsMonHom ((Over.pullback jL).map (OpenSub.incl W)) := inferInstance
        exact @instIsMonHomComp _ _ _ _ _ _ _ _ _ _ _ h1 𝒢.gen_hom }
  exact ⟨𝒢₀, OpenSub.incl W, inferInstanceAs (IsOpenImmersion W.ι), hmon, Scheme.Opens.range_ι W⟩




end SGA3Nbhd

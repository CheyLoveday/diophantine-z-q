import ZInQKernel.Contrib.OneProof.SemiAbelianDescendsPerfect

/-! # chevalley-free, step A: `SemiAbelianDescendsPerfect` from the descent of the quotient

`QuotientDescendsPerfect` is the only thing `semiAbelianDescendsPerfect_of_chevalley` takes from the leaf
`ChevalleyPerfect`: the descent of a semi-abelian presentation `(B', π')` of `U_{k̄}` (`U` smooth, connected, of
finite type over a perfect `k`) to a presentation over `k` with the same kernel over `k̄`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open DictModels.RaynaudOr ZInQ.HeightSplit ZInQ.SemiAbDescend

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ZInQ.ChevFree

/-- **GLUE `QuotientDescendsPerfect`** (descent of the abelian quotient of a semi-abelian group from `k̄` to a
perfect field `k`; the special case of Chevalley's theorem over a perfect field (Conrad 2002 Thm 1.1, Milne AG
8.27, numbers UNVERIFIED) that `semiAbelianDescendsPerfect_of_chevalley` uses). Let `U` be a smooth connected group
scheme of finite type over a perfect field `k`, and let `π' : U_{k̄} → B'` be a faithfully flat homomorphism onto an
abelian variety over `k̄` whose kernel is a split torus (`(Rˣ)^r ≅ ker(U_{k̄}(R) → B'(R))`, naturally in
`k̄`-algebras `R`). Then there is a faithfully flat homomorphism `π : U → B` onto an abelian variety over `k` such
that `π_{k̄}` and `π'` have the same kernel on `R`-points for every `k̄`-algebra `R`. -/
def QuotientDescendsPerfect : Prop :=
  ∀ (k : Type) [Field k] [PerfectField k] (U : Over (Spec (CommRingCat.of k))) [GrpObj U],
    Smooth U.hom → QuasiCompact U.hom → ConnectedSpace U.left →
    letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
    ∀ (B' : PkgI3.AbVar (AlgebraicClosure k)) (π' : (Over.pullback (sφ (φbar k))).obj U ⟶ B'.X),
      IsMonHom π' → Flat π'.left → Surjective π'.left →
      ∀ (r : ℕ) (e : ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R],
          (Fin r → Rˣ) →* (algPt (AlgebraicClosure k) R ⟶ (Over.pullback (sφ (φbar k))).obj U)),
        (∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R], Function.Injective (e R)) →
        (∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R]
          (u : algPt (AlgebraicClosure k) R ⟶ (Over.pullback (sφ (φbar k))).obj U),
          u ≫ π' = 1 ↔ u ∈ (e R).range) →
        (∀ (R S : Type) [CommRing R] [Algebra (AlgebraicClosure k) R] [CommRing S]
          [Algebra (AlgebraicClosure k) S] (f : R →ₐ[AlgebraicClosure k] S) (t : Fin r → Rˣ),
          e S (fun i => Units.map (f : R →* S) (t i)) = algPtMap f ≫ e R t) →
        ∃ (B : PkgI3.AbVar k) (π : U ⟶ B.X),
          letI : GrpObj ((Over.pullback (sφ (φbar k))).obj B.X) := Functor.grpObjObj
          IsMonHom π ∧ Flat π.left ∧ Surjective π.left ∧
          ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R]
            (u : algPt (AlgebraicClosure k) R ⟶ (Over.pullback (sφ (φbar k))).obj U),
            u ≫ (Over.pullback (sφ (φbar k))).map π = 1 ↔ u ≫ π' = 1

open CToPrinted in
theorem semiAbelianDescendsPerfect_of_qd (hQD : QuotientDescendsPerfect) :
    ZInQ.HeightFix.SemiAbelianDescendsPerfect := by
  intro k _ _ G _ _ _ hbar
  have hG : AVGlue.GeomConnOfRationalPoint := geomConnOfRationalPoint_proof
  let φ := φbar k
  let F := Over.pullback (sφ φ)
  letI : GrpObj (F.obj G) := Functor.grpObjObj
  obtain ⟨U', _, inc', hoi', hmh', hcon', B', π', hπm', hfl', hsu', r, e', he_inj', he_ker', he_nat'⟩ :=
    hbar
  haveI := hoi'
  haveI : LocallyOfFiniteType (F.obj G).hom := by
    change LocallyOfFiniteType (pullback.snd G.hom (sφ φ)); infer_instance
  haveI : QuasiCompact (F.obj G).hom := by
    change QuasiCompact (pullback.snd G.hom (sφ φ)); infer_instance
  -- (a) `G⁰` over `k`
  have hW := isSubgroupOpen_W0 G hG
  letI : GrpObj (OpenSub.G0 (W0 G)) := OpenSub.grpG0 hW
  have hinc : IsMonHom (OpenSub.incl (W0 G)) := OpenSub.isMonHom_incl hW
  let U := OpenSub.G0 (W0 G)
  let incl : U ⟶ G := OpenSub.incl (W0 G)
  haveI : IsOpenImmersion incl.left := inferInstanceAs (IsOpenImmersion (W0 G).ι)
  haveI : LocallyOfFiniteType ((W0 G).ι ≫ G.hom) := inferInstance
  haveI : QuasiCompact ((W0 G).ι ≫ G.hom) := quasiCompact_of_openImm incl
  haveI : LocallyOfFiniteType U.hom := inferInstanceAs (LocallyOfFiniteType ((W0 G).ι ≫ G.hom))
  haveI : QuasiCompact U.hom := inferInstanceAs (QuasiCompact ((W0 G).ι ≫ G.hom))
  have hconnU : ConnectedSpace U.left := connectedSpace_W0 G
  letI : GrpObj (F.obj U) := Functor.grpObjObj
  have hconnFU : ConnectedSpace (F.obj U).left :=
    connectedSpace_pullback_idComp hG G (W0 G) rfl (AlgebraicClosure k) (sφ φ)
  haveI : QuasiCompact (F.obj U).hom := by
    change QuasiCompact (pullback.snd U.hom (sφ φ)); infer_instance
  -- (b) `U' = (G⁰)_{k̄}` inside `G_{k̄}`
  let p := pullback.fst G.hom (sφ φ)
  have hsq := pbmap_isPullback (sφ φ) U G incl
  haveI hFinc : IsOpenImmersion (F.map incl).left :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hsq (inferInstanceAs (IsOpenImmersion (W0 G).ι))
  have hrangeU : Set.range (F.map incl).left = p ⁻¹' (idCompSet G) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      show p ((F.map incl).left y) ∈ idCompSet G
      rw [← Scheme.Hom.comp_apply, ← hsq.w, Scheme.Hom.comp_apply]
      have : incl.left (pullback.fst U.hom (sφ φ) y) ∈ Set.range (W0 G).ι := ⟨_, rfl⟩
      rwa [Scheme.Opens.range_ι] at this
    · intro hx
      have hx' : p x ∈ Set.range (W0 G).ι := by rw [Scheme.Opens.range_ι]; exact hx
      obtain ⟨u, hu⟩ := hx'
      obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := incl.left) (g := p) u x hu
      refine ⟨hsq.isoPullback.inv z, ?_⟩
      rw [← Scheme.Hom.comp_apply, hsq.isoPullback_inv_snd, hz2]
  let pt : (𝟙_ (Over (Spec (CommRingCat.of (AlgebraicClosure k))))).left :=
    (default : Spec (CommRingCat.of (AlgebraicClosure k)))
  let ebar := (η[F.obj G] : 𝟙_ _ ⟶ F.obj G).left pt
  have he1 : ebar ∈ Set.range inc'.left :=
    ⟨(η[U'] : 𝟙_ _ ⟶ U').left pt, by rw [← Scheme.Hom.comp_apply, ← Over.comp_left, IsMonHom.one_hom inc']⟩
  have he2 : ebar ∈ p ⁻¹' idCompSet G := by
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, unit_bc_fst, Scheme.Hom.comp_apply]
    exact idCompSet_one G _
  have hclo : IsClopen (p ⁻¹' idCompSet G) :=
    ⟨(isClosed_idCompSet G).preimage p.continuous, (isOpen_idCompSet G).preimage p.continuous⟩
  have hsub1 : Set.range inc'.left ⊆ p ⁻¹' idCompSet G :=
    (isConnected_range inc'.left.continuous).isPreconnected.subset_isClopen hclo ⟨ebar, he1, he2⟩
  have hR'clo : IsClopen (Set.range inc'.left) :=
    ⟨isClosed_range_openSubgroup inc', inc'.left.isOpenEmbedding.isOpen_range⟩
  have hpre : _root_.IsPreconnected (p ⁻¹' idCompSet G) := by
    rw [← hrangeU]; exact (isConnected_range (F.map incl).left.continuous).isPreconnected
  have hsub2 : p ⁻¹' idCompSet G ⊆ Set.range inc'.left :=
    hpre.subset_isClopen hR'clo ⟨ebar, he2, he1⟩
  have heq : Set.range (F.map incl).left = Set.range inc'.left := by
    rw [hrangeU]; exact hsub2.antisymm hsub1
  let isoS := IsOpenImmersion.isoOfRangeEq (F.map incl).left inc'.left heq
  have hfac : isoS.hom ≫ inc'.left = (F.map incl).left := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  let φU : F.obj U ≅ U' := Over.isoMk isoS (by
    have h1 : U'.hom = inc'.left ≫ (F.obj G).hom := (Over.w inc').symm
    rw [h1, ← Category.assoc, hfac]; exact Over.w (F.map incl))
  have hφU : φU.hom ≫ inc' = F.map incl := by
    apply Over.OverMorphism.ext; exact hfac
  haveI : Mono inc' := ⟨fun g h hgh => Over.OverMorphism.ext ((cancel_mono inc'.left).mp
    (by simpa using congrArg CommaMorphism.left hgh))⟩
  haveI : IsMonHom (φU.hom ≫ inc') := by rw [hφU]; infer_instance
  haveI : IsMonHom φU.hom := isMonHom_of_comp_mono φU.hom inc'
  haveI : IsMonHom (φU.inv ≫ φU.hom) := by rw [Iso.inv_hom_id]; infer_instance
  haveI : IsMonHom φU.inv := isMonHom_of_comp_mono φU.inv φU.hom
  -- (c) the kernels of `π'` and of `φU ≫ π'` are split tori
  have hkerπ' := isSmoothConnAffineKer_of_torus π' r e' he_inj' he_ker' he_nat'
  let e2 : ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R],
      (Fin r → Rˣ) →* (algPt (AlgebraicClosure k) R ⟶ F.obj U) :=
    fun R _ _ => (IsMonHom.monoidHom φU.inv (algPt _ R)).comp (e' R)
  have he2_apply : ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R] (t : Fin r → Rˣ),
      e2 R t = e' R t ≫ φU.inv := fun _ _ _ _ => rfl
  have he_inj2 : ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R],
      Function.Injective (e2 R) := by
    intro R _ _ t₁ t₂ h
    rw [he2_apply, he2_apply] at h
    exact he_inj' R ((cancel_mono φU.inv).mp h)
  have he_ker2 : ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R]
      (u : algPt (AlgebraicClosure k) R ⟶ F.obj U), u ≫ (φU.hom ≫ π') = 1 ↔ u ∈ (e2 R).range := by
    intro R _ _ u
    rw [← Category.assoc, he_ker' R (u ≫ φU.hom)]
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨t, by rw [he2_apply, ht, Category.assoc, Iso.hom_inv_id, Category.comp_id]⟩
    · rintro ⟨t, rfl⟩
      exact ⟨t, by rw [he2_apply, Category.assoc, Iso.inv_hom_id, Category.comp_id]⟩
  have he_nat2 : ∀ (R S : Type) [CommRing R] [Algebra (AlgebraicClosure k) R] [CommRing S]
      [Algebra (AlgebraicClosure k) S] (f : R →ₐ[AlgebraicClosure k] S) (t : Fin r → Rˣ),
      e2 S (fun i => Units.map (f : R →* S) (t i)) = algPtMap f ≫ e2 R t := by
    intro R S _ _ _ _ f t
    rw [he2_apply, he2_apply, he_nat', Category.assoc]
  -- (d) smoothness: `U'`, `(G⁰)_{k̄}`, `G⁰`
  haveI : LocallyOfFiniteType U'.hom := by rw [← Over.w inc']; infer_instance
  haveI : QuasiCompact U'.hom := quasiCompact_of_openImm inc'
  haveI : IsLocallyNoetherian U'.left := LocallyOfFiniteType.isLocallyNoetherian U'.hom
  haveI : CompactSpace U'.left := QuasiCompact.compactSpace_of_compactSpace U'.hom
  haveI : IsNoetherian U'.left := {}
  have hsmU' : Smooth U'.hom := smooth_of_smoothKer π' hfl' hsu' inferInstance hkerπ'.1
  have hsmFU : Smooth (F.obj U).hom := by
    rw [← Over.w φU.hom]
    haveI : IsIso φU.hom.left := by change IsIso ((Over.forget _).map φU.hom); infer_instance
    infer_instance
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) (sφ φ) :=
    ⟨⟨⟨fun x => ⟨default, Subsingleton.elim _ _⟩⟩, inferInstance⟩, inferInstance⟩
  have hsmU : Smooth U.hom :=
    MorphismProperty.of_pullback_snd_of_descendsAlong (P := @Smooth)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (f := U.hom) (g := sφ φ) hQ hsmFU
  -- (e) descent of the quotient `(B', φU ≫ π')` to `k`
  haveI : IsIso φU.hom.left := by change IsIso ((Over.forget _).map φU.hom); infer_instance
  have hfl2 : Flat (φU.hom ≫ π').left := by
    haveI := hfl'; change Flat (φU.hom.left ≫ π'.left); infer_instance
  have hsu2 : Surjective (φU.hom ≫ π').left := by
    haveI := hsu'; change Surjective (φU.hom.left ≫ π'.left); infer_instance
  obtain ⟨B, π, hπm, hπfl, hπsu, huniq⟩ :=
    hQD k U hsmU inferInstance hconnU B' (φU.hom ≫ π') inferInstance hfl2 hsu2 r e2 he_inj2 he_ker2 he_nat2
  haveI := hπm
  letI : GrpObj (F.obj B.X) := Functor.grpObjObj
  -- (f) assemble
  refine ⟨U, inferInstance, incl, inferInstanceAs (IsOpenImmersion (W0 G).ι), hinc, hconnU, B, π, hπm,
    hπfl, hπsu, r, fun R _ _ => (Φ φ U R).toMonoidHom.comp (e2 R), ?_, ?_, ?_⟩
  · intro R _ _
    exact (Φ φ U R).injective.comp (he_inj2 R)
  · intro R _ _ u
    letI := algK φ R
    have h1 : u ≫ π = 1 ↔ (Φ φ U R).symm u ≫ F.map π = 1 := by
      constructor
      · intro h
        apply (Φ φ B.X R).injective
        rw [Φ_comp, MulEquiv.apply_symm_apply, h, map_one]
      · intro h
        have := congrArg (Φ φ B.X R) h
        rwa [Φ_comp, MulEquiv.apply_symm_apply, map_one] at this
    rw [h1, huniq, he_ker2]
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨t, by simp [ht]⟩
    · rintro ⟨t, ht⟩
      refine ⟨t, ?_⟩
      simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply] at ht
      rw [← ht, MulEquiv.symm_apply_apply]
  · intro R S _ _ _ _ f t
    letI := algK φ R
    letI := algK φ S
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply]
    rw [he_nat2 R S f t, Φ_natural]

end ZInQ.ChevFree
#print axioms ZInQ.ChevFree.semiAbelianDescendsPerfect_of_qd

import ZInQKernel.Contrib.OneProof.BLRLocalizes

/-!
# Part B: Néron models commute with ind-smooth base change

`R → R₁` such that every finite subset of `R₁` lies in an `R`-subalgebra smooth over `R`, and
`Spec K₁ = Spec R₁ ×_{Spec R} Spec K`. Then the base change of a Néron model over `R` is a Néron model over `R₁`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CategoryTheory Limits AlgebraicGeometry

namespace NeronSH

/-! ## `Spec R₁ = lim Spec Bᵢ` for a directed family of subalgebras with union `R₁` -/

section Family

variable {R R₁ : Type} [CommRing R] [CommRing R₁] [Algebra R R₁]
  {ι : Type} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] (B : ι → Subalgebra R R₁) (hB : Monotone B)

/-- The inclusion `Bᵢ → Bⱼ`. -/
noncomputable def incl {i j : ι} (h : i ≤ j) : B i →+* B j := (Subalgebra.inclusion (hB h)).toRingHom

theorem incl_val {i j : ι} (h : i ≤ j) (x : B i) : ((incl B hB h x : B j) : R₁) = x := rfl

/-- The diagram `i ↦ Bᵢ`. -/
noncomputable def ringDiag : ι ⥤ CommRingCat.{0} where
  obj i := CommRingCat.of (B i)
  map f := CommRingCat.ofHom (incl B hB (leOfHom f))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- `R₁` as a cocone. -/
noncomputable def ringCocone : Cocone (ringDiag B hB) where
  pt := CommRingCat.of R₁
  ι := { app i := CommRingCat.ofHom (B i).val.toRingHom
         naturality _ _ _ := rfl }

/-- **`R₁ = colim Bᵢ`.** -/
noncomputable def ringCoconeIsColimit (hcov : ∀ x : R₁, ∃ i, x ∈ B i) :
    IsColimit (ringCocone B hB) := by
  haveI : ReflectsColimit (ringDiag B hB) (forget CommRingCat) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  refine isColimitOfReflects (forget CommRingCat) (Types.FilteredColimit.isColimitOf' _ _ ?_ ?_)
  · intro (x : R₁)
    obtain ⟨i, hi⟩ := hcov x
    exact ⟨i, (⟨x, hi⟩ : B i), rfl⟩
  · intro i x y h
    refine ⟨i, 𝟙 i, ?_⟩
    have : (x : B i) = y := Subtype.ext h
    rw [this]

/-- The diagram `i ↦ Spec Bᵢ`. -/
noncomputable def specDiag : ιᵒᵖ ⥤ Scheme.{0} where
  obj i := Spec (CommRingCat.of (B i.unop))
  map f := Spec.map (CommRingCat.ofHom (incl B hB (leOfHom f.unop)))
  map_id i := by rw [← Spec.map_id]; rfl
  map_comp f g := by rw [← Spec.map_comp]; rfl

/-- `Spec R₁` as a cone. -/
noncomputable def specCone : Cone (specDiag B hB) where
  pt := Spec (CommRingCat.of R₁)
  π :=
    { app i := Spec.map (CommRingCat.ofHom (B i.unop).val.toRingHom)
      naturality i j f := by
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, specDiag]
        rw [← Spec.map_comp]
        rfl }

theorem specCone_π_app (i : ιᵒᵖ) :
    (specCone B hB).π.app i = Spec.map (CommRingCat.ofHom (B i.unop).val.toRingHom) := rfl

/-- **`Spec R₁ = lim Spec Bᵢ`.** -/
noncomputable def specConeIsLimit (hcov : ∀ x : R₁, ∃ i, x ∈ B i) : IsLimit (specCone B hB) := by
  have h := isLimitOfPreserves Scheme.Spec (ringCoconeIsColimit B hB hcov).op
  refine (IsLimit.equivOfNatIsoOfIso (NatIso.ofComponents (fun _ => Iso.refl _) ?_) _ _
    (Cone.ext (Iso.refl _) ?_)) h
  · intro m n f
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · intro n
    simp only [Iso.refl_hom, Category.id_comp]

instance specDiag_isAffineHom {i j : ιᵒᵖ} (f : i ⟶ j) : IsAffineHom ((specDiag B hB).map f) :=
  show IsAffineHom (Spec.map _) from inferInstance

instance specDiag_compactSpace (i : ιᵒᵖ) : CompactSpace ((specDiag B hB).obj i) :=
  show CompactSpace (Spec _) from inferInstance

instance specDiag_quasiSeparatedSpace (i : ιᵒᵖ) :
    QuasiSeparatedSpace ((specDiag B hB).obj i) :=
  show QuasiSeparatedSpace (Spec _) from inferInstance

/-- `Spec Bᵢ → Spec R`. -/
noncomputable def ej (i : ιᵒᵖ) : (specDiag B hB).obj i ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (B i.unop)))

theorem smooth_ej (i : ιᵒᵖ) [Algebra.Smooth R (B i.unop)] : Smooth (ej B hB i) := by
  have : Smooth (Spec.map (CommRingCat.ofHom (algebraMap R (B i.unop)))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    exact RingHom.smooth_algebraMap.mpr inferInstance
  exact this

theorem π_ej (i : ιᵒᵖ) : (specCone B hB).π.app i ≫ ej B hB i =
    Spec.map (CommRingCat.ofHom (algebraMap R R₁)) := by
  refine (Spec.map_comp (CommRingCat.ofHom (algebraMap R (B i.unop)))
    (CommRingCat.ofHom (B i.unop).val.toRingHom)).symm.trans ?_
  rfl

theorem map_ej {i j : ιᵒᵖ} (f : i ⟶ j) : (specDiag B hB).map f ≫ ej B hB j = ej B hB i := by
  refine (Spec.map_comp (CommRingCat.ofHom (algebraMap R (B j.unop)))
    (CommRingCat.ofHom (incl B hB (leOfHom f.unop)))).symm.trans ?_
  rfl

open ZInQ.Contrib.SpreadOut in
/-- **Spreading out** (EGA IV 8.8.2 (ii), 17.7.8 (ii), proved in the tree): a smooth affine `R₁`-scheme is the base
change of a smooth scheme over some `Spec Bᵢ`. -/
theorem exists_spread (hcov : ∀ x : R₁, ∃ i, x ∈ B i) (V : Scheme.{0}) [IsAffine V]
    (v : V ⟶ Spec (CommRingCat.of R₁)) [Smooth v] :
    ∃ (a : ιᵒᵖ) (W : Over ((specDiag B hB).obj a)) (φ : V ⟶ W.left),
      Smooth W.hom ∧ IsPullback φ v W.hom ((specCone B hB).π.app a) := by
  haveI : IsAffineHom v := inferInstance
  haveI : LocallyOfFinitePresentation (Over.mk v).hom := (inferInstance : LocallyOfFinitePresentation v)
  haveI : QuasiCompact (Over.mk v).hom := (inferInstance : QuasiCompact v)
  haveI : QuasiSeparated (Over.mk v).hom := (inferInstance : QuasiSeparated v)
  obtain ⟨i, Xi, hl, hq, hs, ⟨e⟩⟩ := EGAIV_8_8_2_ii_proof ι (specDiag B hB) (specCone B hB)
    (specConeIsLimit B hB hcov) (Over.mk v) (inferInstance : LocallyOfFinitePresentation v)
    (inferInstance : QuasiCompact v) (inferInstance : QuasiSeparated v)
  haveI : Smooth (Over.mk v).hom := ‹Smooth v›
  have hsm : Smooth ((Over.pullback ((specCone B hB).π.app i)).obj Xi).hom :=
    @smooth_of_iso _ _ (Over.mk v) e ‹Smooth v›
  obtain ⟨j, a, hj⟩ := EGAIV_17_7_8_ii_proof ι (specDiag B hB) (specCone B hB)
    (specConeIsLimit B hB hcov) i Xi hl hq hs hsm
  have hw : e.inv.left ≫ pullback.snd Xi.hom ((specCone B hB).π.app i) = v := Over.w e.inv
  have hπ : (specCone B hB).π.app j ≫ (specDiag B hB).map a = (specCone B hB).π.app i :=
    (specCone B hB).w a
  have hc0 : (e.inv.left ≫ pullback.fst Xi.hom ((specCone B hB).π.app i)) ≫ Xi.hom =
      v ≫ (specCone B hB).π.app i := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hw]
    exact rfl
  have hcomm : (e.inv.left ≫ pullback.fst Xi.hom ((specCone B hB).π.app i)) ≫ Xi.hom =
      (v ≫ (specCone B hB).π.app j) ≫ (specDiag B hB).map a :=
    hc0.trans ((congrArg (fun t => v ≫ t) hπ.symm).trans (Category.assoc _ _ _).symm)
  let φ : V ⟶ pullback Xi.hom ((specDiag B hB).map a) := pullback.lift _ _ hcomm
  refine ⟨j, (Over.pullback ((specDiag B hB).map a)).obj Xi, φ, hj, ?_⟩
  have houter : IsPullback (e.inv.left ≫ pullback.fst Xi.hom ((specCone B hB).π.app i)) v Xi.hom
      ((specCone B hB).π.app i) :=
    IsPullback.of_iso_pullback ⟨hc0⟩ ((Over.forget _).mapIso e.symm) rfl hw
  have h1 : φ ≫ pullback.fst _ _ = e.inv.left ≫ pullback.fst Xi.hom ((specCone B hB).π.app i) :=
    pullback.lift_fst _ _ _
  refine IsPullback.of_right (h₁₂ := pullback.fst Xi.hom ((specDiag B hB).map a))
    (h₂₂ := (specDiag B hB).map a) ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  rw [h1]; erw [hπ]; exact houter

end Family


end NeronSH

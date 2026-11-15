import Mathlib
import ZInQKernel.Contrib.CloudW01Spread.FinitePresentation
import ZInQKernel.Contrib.CloudW01Spread.Smooth
import ZInQKernel.Contrib.SmoothFibre.Basic

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry

namespace GapBLR

/-! ## `R_𝔭` as a cofiltered limit of `Spec R[1/s]`, `s ∉ 𝔭` -/

section Diagram

variable {R : Type} [CommRing R] (𝔭 : Ideal R) [𝔭.IsPrime]

/-- The index set: elements `s ∉ 𝔭`, preordered by divisibility. -/
structure Idx where
  /-- the element -/
  s : R
  hs : s ∉ 𝔭

instance : Preorder (Idx 𝔭) where
  le a b := a.s ∣ b.s
  le_refl a := dvd_refl _
  le_trans _ _ _ := dvd_trans

instance : IsDirectedOrder (Idx 𝔭) where
  directed a b := ⟨⟨a.s * b.s, fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim a.hs b.hs⟩,
    dvd_mul_right _ _, dvd_mul_left _ _⟩

instance : Nonempty (Idx 𝔭) := ⟨⟨1, fun h => (Ideal.IsPrime.ne_top ‹_›) ((Ideal.eq_top_iff_one _).2 h)⟩⟩

variable {𝔭}

/-- `R[1/s]`. -/
abbrev Loc (a : Idx 𝔭) : Type := Localization.Away a.s

theorem isUnit_le {a b : Idx 𝔭} (h : a ≤ b) : IsUnit (algebraMap R (Loc b) a.s) :=
  isUnit_of_dvd_unit (map_dvd _ h) (IsLocalization.Away.algebraMap_isUnit b.s)

/-- The transition map `R[1/s] → R[1/t]` for `s ∣ t`. -/
noncomputable def tr {a b : Idx 𝔭} (h : a ≤ b) : Loc a →+* Loc b :=
  IsLocalization.Away.lift a.s (isUnit_le h)

theorem tr_alg {a b : Idx 𝔭} (h : a ≤ b) (x : R) :
    tr h (algebraMap R (Loc a) x) = algebraMap R (Loc b) x :=
  IsLocalization.Away.lift_eq _ _ _

theorem hom_ext' {a : Idx 𝔭} {T : Type*} [CommRing T] {f g : Loc a →+* T}
    (h : ∀ x : R, f (algebraMap R (Loc a) x) = g (algebraMap R (Loc a) x)) : f = g :=
  IsLocalization.ringHom_ext (Submonoid.powers a.s) (RingHom.ext h)

variable (R𝔭 : Type) [CommRing R𝔭] [Algebra R R𝔭] [IsLocalization.AtPrime R𝔭 𝔭]

theorem isUnit_P (a : Idx 𝔭) : IsUnit (algebraMap R R𝔭 a.s) :=
  IsLocalization.map_units R𝔭 (⟨a.s, a.hs⟩ : 𝔭.primeCompl)

/-- `R[1/s] → R_𝔭`. -/
noncomputable def toP (a : Idx 𝔭) : Loc a →+* R𝔭 :=
  IsLocalization.Away.lift a.s (isUnit_P R𝔭 a)

theorem toP_alg (a : Idx 𝔭) (x : R) : toP R𝔭 a (algebraMap R (Loc a) x) = algebraMap R R𝔭 x :=
  IsLocalization.Away.lift_eq _ _ _

variable (𝔭)

/-- The diagram `s ↦ R[1/s]`. -/
noncomputable def ringDiag : Idx 𝔭 ⥤ CommRingCat.{0} where
  obj a := CommRingCat.of (Loc a)
  map f := CommRingCat.ofHom (tr (leOfHom f))
  map_id a := by
    apply CommRingCat.hom_ext
    exact hom_ext' (fun x => by simp [tr_alg])
  map_comp f g := by
    apply CommRingCat.hom_ext
    exact hom_ext' (fun x => by simp [tr_alg])

/-- `R_𝔭` as a cocone. -/
noncomputable def ringCocone : Cocone (ringDiag 𝔭) where
  pt := CommRingCat.of R𝔭
  ι :=
    { app a := CommRingCat.ofHom (toP R𝔭 a)
      naturality a b f := by
        apply CommRingCat.hom_ext
        exact hom_ext' (fun x => by simp [ringDiag, tr_alg, toP_alg]) }

/-- **`R_𝔭 = colim_{s ∉ 𝔭} R[1/s]`.** -/
noncomputable def ringCoconeIsColimit : IsColimit (ringCocone 𝔭 R𝔭) := by
  haveI : ReflectsColimit (ringDiag 𝔭) (forget CommRingCat) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  refine isColimitOfReflects (forget CommRingCat) (Types.FilteredColimit.isColimitOf' _ _ ?_ ?_)
  · intro (x : R𝔭)
    obtain ⟨⟨r, t⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔭.primeCompl x
    let a : Idx 𝔭 := ⟨t.1, t.2⟩
    refine ⟨a, (IsLocalization.mk' (Loc a) r (⟨t.1, Submonoid.mem_powers _⟩ : Submonoid.powers a.s) :
      Loc a), ?_⟩
    show _ = toP R𝔭 a _
    rw [IsLocalization.mk'_eq_iff_eq_mul, ← toP_alg R𝔭 a, ← toP_alg R𝔭 a, ← map_mul]
    congr 1
    exact (IsLocalization.mk'_spec (Loc a) r (⟨t.1, Submonoid.mem_powers _⟩ : Submonoid.powers a.s)).symm
  · intro a x' y' h
    let x : Loc a := x'
    let y : Loc a := y'
    have h' : toP R𝔭 a x = toP R𝔭 a y := h
    obtain ⟨⟨r, ⟨_, n, rfl⟩⟩, hz0⟩ := IsLocalization.mk'_surjective (Submonoid.powers a.s) (x - y)
    have hz : IsLocalization.mk' (Loc a) r (⟨_, n, rfl⟩ : Submonoid.powers a.s) = x - y := hz0
    have h0 : toP R𝔭 a (x - y) = 0 := by rw [map_sub, h', sub_self]
    have hr : algebraMap R R𝔭 r = 0 := by
      rw [← toP_alg R𝔭 a, ← IsLocalization.mk'_spec (Loc a) r (⟨_, n, rfl⟩ : Submonoid.powers a.s), map_mul, hz, h0, zero_mul]
    obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff 𝔭.primeCompl R𝔭 r).1 hr
    let b : Idx 𝔭 := ⟨a.s * m.1, fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim a.hs m.2⟩
    have hab : a ≤ b := dvd_mul_right _ _
    refine ⟨b, homOfLE hab, ?_⟩
    show tr hab x = tr hab y
    rw [← sub_eq_zero, ← map_sub, ← hz]
    have hmu : IsUnit (algebraMap R (Loc b) m.1) :=
      isUnit_of_dvd_unit (map_dvd _ (dvd_mul_left m.1 a.s)) (IsLocalization.Away.algebraMap_isUnit b.s)
    have hrb : algebraMap R (Loc b) r = 0 := by
      have : algebraMap R (Loc b) (m.1 * r) = 0 := by rw [hm, map_zero]
      rw [map_mul] at this
      exact (hmu.mul_right_eq_zero).1 this
    have hsu : IsUnit (algebraMap R (Loc b) (a.s ^ n)) := by rw [map_pow]; exact (isUnit_le hab).pow n
    have key := congrArg (tr hab) (IsLocalization.mk'_spec (Loc a) r (⟨_, n, rfl⟩ : Submonoid.powers a.s))
    rw [map_mul, tr_alg, tr_alg, hrb] at key
    exact (hsu.mul_left_eq_zero).1 key

/-- The diagram `s ↦ Spec R[1/s]`. -/
noncomputable def specDiag : (Idx 𝔭)ᵒᵖ ⥤ Scheme.{0} where
  obj a := Spec (CommRingCat.of (Loc a.unop))
  map f := Spec.map (CommRingCat.ofHom (tr (leOfHom f.unop)))
  map_id a := by
    rw [← Spec.map_id]
    congr 1
    apply CommRingCat.hom_ext
    exact hom_ext' (fun x => by simp [tr_alg])
  map_comp f g := by
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact hom_ext' (fun x => by simp [tr_alg])

/-- `Spec R_𝔭` as a cone. -/
noncomputable def specCone : Cone (specDiag 𝔭) where
  pt := Spec (CommRingCat.of R𝔭)
  π :=
    { app a := Spec.map (CommRingCat.ofHom (toP R𝔭 a.unop))
      naturality a b f := by
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, specDiag]
        rw [← Spec.map_comp]
        congr 1
        apply CommRingCat.hom_ext
        exact hom_ext' (fun x => by simp [tr_alg, toP_alg]) }

theorem specCone_π_app (a : (Idx 𝔭)ᵒᵖ) :
    (specCone 𝔭 R𝔭).π.app a = Spec.map (CommRingCat.ofHom (toP R𝔭 a.unop)) := rfl

/-- **`Spec R_𝔭 = lim_{s ∉ 𝔭} Spec R[1/s]`.** -/
noncomputable def specConeIsLimit : IsLimit (specCone 𝔭 R𝔭) := by
  have h := isLimitOfPreserves Scheme.Spec (ringCoconeIsColimit 𝔭 R𝔭).op
  refine (IsLimit.equivOfNatIsoOfIso (NatIso.ofComponents (fun _ => Iso.refl _) ?_) _ _
    (Cone.ext (Iso.refl _) ?_)) h
  · intro m n f
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · intro n
    simp only [Iso.refl_hom, Category.id_comp]

instance specDiag_isAffineHom {i j : (Idx 𝔭)ᵒᵖ} (f : i ⟶ j) : IsAffineHom ((specDiag 𝔭).map f) :=
  show IsAffineHom (Spec.map _) from inferInstance

instance specDiag_compactSpace (i : (Idx 𝔭)ᵒᵖ) : CompactSpace ((specDiag 𝔭).obj i) :=
  show CompactSpace (Spec _) from inferInstance

instance specDiag_quasiSeparatedSpace (i : (Idx 𝔭)ᵒᵖ) :
    QuasiSeparatedSpace ((specDiag 𝔭).obj i) :=
  show QuasiSeparatedSpace (Spec _) from inferInstance

variable {𝔭}

/-- `Spec R[1/s] → Spec R`, an open immersion. -/
noncomputable def ej (a : (Idx 𝔭)ᵒᵖ) : (specDiag 𝔭).obj a ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (Loc a.unop)))

instance (a : (Idx 𝔭)ᵒᵖ) : IsOpenImmersion (ej a) :=
  IsOpenImmersion.of_isLocalization a.unop.s

theorem π_ej (a : (Idx 𝔭)ᵒᵖ) : (specCone 𝔭 R𝔭).π.app a ≫ ej a =
    Spec.map (CommRingCat.ofHom (algebraMap R R𝔭)) := by
  refine (Spec.map_comp (CommRingCat.ofHom (algebraMap R (Loc a.unop)))
    (CommRingCat.ofHom (toP R𝔭 a.unop))).symm.trans ?_
  congr 1
  apply CommRingCat.hom_ext
  ext x
  exact toP_alg R𝔭 a.unop x

theorem toP_ej (a : (Idx 𝔭)ᵒᵖ) : Spec.map (CommRingCat.ofHom (toP R𝔭 a.unop)) ≫ ej a =
    Spec.map (CommRingCat.ofHom (algebraMap R R𝔭)) :=
  π_ej R𝔭 a

/-! ## Spreading out a smooth affine `R_𝔭`-scheme -/

open ZInQ.Contrib.SpreadOut in
/-- **Spreading out.** A smooth affine scheme `V` over `Spec R_𝔭` is the base change of a smooth scheme
`W` over some `Spec R[1/s]`, `s ∉ 𝔭` (EGA IV 8.8.2 (ii) and 17.7.8 (ii), both proved in
`ZInQKernel/Contrib/CloudW01Spread`). -/
theorem exists_spread (V : Scheme.{0}) [IsAffine V] (v : V ⟶ Spec (CommRingCat.of R𝔭)) [Smooth v] :
    ∃ (a : (Idx 𝔭)ᵒᵖ) (W : Over ((specDiag 𝔭).obj a)) (φ : V ⟶ W.left),
      Smooth W.hom ∧ IsPullback φ v W.hom ((specCone 𝔭 R𝔭).π.app a) := by
  haveI : IsAffineHom v := inferInstance
  haveI : LocallyOfFinitePresentation (Over.mk v).hom := (inferInstance : LocallyOfFinitePresentation v)
  haveI : QuasiCompact (Over.mk v).hom := (inferInstance : QuasiCompact v)
  haveI : QuasiSeparated (Over.mk v).hom := (inferInstance : QuasiSeparated v)
  obtain ⟨i, Xi, hl, hq, hs, ⟨e⟩⟩ := EGAIV_8_8_2_ii_proof (Idx 𝔭) (specDiag 𝔭) (specCone 𝔭 R𝔭)
    (specConeIsLimit 𝔭 R𝔭) (Over.mk v) (inferInstance : LocallyOfFinitePresentation v)
    (inferInstance : QuasiCompact v) (inferInstance : QuasiSeparated v)
  haveI : Smooth (Over.mk v).hom := ‹Smooth v›
  have hsm : Smooth ((Over.pullback ((specCone 𝔭 R𝔭).π.app i)).obj Xi).hom := @smooth_of_iso _ _ (Over.mk v) e ‹Smooth v›
  obtain ⟨j, a, hj⟩ := EGAIV_17_7_8_ii_proof (Idx 𝔭) (specDiag 𝔭) (specCone 𝔭 R𝔭)
    (specConeIsLimit 𝔭 R𝔭) i Xi hl hq hs hsm
  have hw : e.inv.left ≫ pullback.snd Xi.hom ((specCone 𝔭 R𝔭).π.app i) = v := Over.w e.inv
  have hπ : (specCone 𝔭 R𝔭).π.app j ≫ (specDiag 𝔭).map a = (specCone 𝔭 R𝔭).π.app i :=
    (specCone 𝔭 R𝔭).w a
  have hc0 : (e.inv.left ≫ pullback.fst Xi.hom ((specCone 𝔭 R𝔭).π.app i)) ≫ Xi.hom =
      v ≫ (specCone 𝔭 R𝔭).π.app i := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hw]
    exact rfl
  have hcomm : (e.inv.left ≫ pullback.fst Xi.hom ((specCone 𝔭 R𝔭).π.app i)) ≫ Xi.hom =
      (v ≫ (specCone 𝔭 R𝔭).π.app j) ≫ (specDiag 𝔭).map a :=
    hc0.trans ((congrArg (fun t => v ≫ t) hπ.symm).trans (Category.assoc _ _ _).symm)
  let φ : V ⟶ pullback Xi.hom ((specDiag 𝔭).map a) := pullback.lift _ _ hcomm
  refine ⟨j, (Over.pullback ((specDiag 𝔭).map a)).obj Xi, φ, hj, ?_⟩
  have houter : IsPullback (e.inv.left ≫ pullback.fst Xi.hom ((specCone 𝔭 R𝔭).π.app i)) v Xi.hom
      ((specCone 𝔭 R𝔭).π.app i) :=
    IsPullback.of_iso_pullback ⟨hc0⟩ ((Over.forget _).mapIso e.symm) rfl hw
  have h1 : φ ≫ pullback.fst _ _ = e.inv.left ≫ pullback.fst Xi.hom ((specCone 𝔭 R𝔭).π.app i) :=
    pullback.lift_fst _ _ _
  refine IsPullback.of_right (h₁₂ := pullback.fst Xi.hom ((specDiag 𝔭).map a))
    (h₂₂ := (specDiag 𝔭).map a) ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  rw [h1]; erw [hπ]; exact houter

end Diagram

/-! ## Scheme-level lemmas -/

section Lemmas

/-- An affine scheme smooth over a field is reduced (from `ZInQ.SmoothFibre.isReduced_of_smooth_of_field`). -/
theorem isReduced_of_smooth_field_affine {K : Type} [Field K] {Z : Scheme.{0}} [IsAffine Z]
    (q : Z ⟶ Spec (CommRingCat.of K)) [Smooth q] : IsReduced Z := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (Z.isoSpec.inv ≫ q)
  have hs : Smooth (Spec.map φ) := by rw [hφ]; infer_instance
  have hφs : φ.hom.Smooth := HasRingHomProperty.Spec_iff.mp hs
  letI := φ.hom.toAlgebra
  haveI : Algebra.Smooth K Γ(Z, ⊤) := hφs
  haveI : _root_.IsReduced Γ(Z, ⊤) := ZInQ.SmoothFibre.isReduced_of_smooth_of_field K _
  exact isReduced_of_isAffine_isReduced Z

/-- A scheme smooth over a field is reduced. -/
theorem isReduced_of_smooth_field {K : Type} [Field K] {P : Scheme.{0}}
    (q : P ⟶ Spec (CommRingCat.of K)) [Smooth q] : IsReduced P := by
  haveI : ∀ i, IsReduced (P.affineCover.X i) := fun i =>
    isReduced_of_smooth_field_affine (P.affineCover.f i ≫ q)
  exact IsReduced.of_openCover (𝒰 := P.affineCover)

end Lemmas

/-- (dev copy of `CToPrinted.IsNeronModelOver`, verbatim) -/
def IsNeronModelOver (R K : Type) [CommRing R] [Field K] [Algebra R K]
    (X : Over (Spec (CommRingCat.of R))) : Prop :=
  Smooth X.hom ∧ IsSeparated X.hom ∧ LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom ∧
    ∀ (Y : Over (Spec (CommRingCat.of R))) [Smooth Y.hom],
      Function.Bijective fun f : Y ⟶ X =>
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map f

/-! ## The Néron property, at `R` and at `R_𝔭` -/

section Main

variable {R K : Type} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  {𝔭 : Ideal R} [𝔭.IsPrime] (R𝔭 : Type) [CommRing R𝔭] [Algebra R R𝔭] [IsLocalization.AtPrime R𝔭 𝔭]
  [Algebra R𝔭 K] [IsScalarTower R R𝔭 K]

include 𝔭

/-- `R_𝔭 → K` is injective. -/
theorem algebraMap_P_injective : Function.Injective (algebraMap R𝔭 K) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨⟨r, t⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔭.primeCompl z
  have h := IsLocalization.mk'_spec R𝔭 r t
  have h2 := congrArg (algebraMap R𝔭 K) h
  rw [map_mul, hz, zero_mul, ← IsScalarTower.algebraMap_apply] at h2
  have hr : r = 0 := (IsFractionRing.injective R K) (by rw [← h2, map_zero])
  subst hr; exact IsLocalization.mk'_zero _

theorem isReduced_P (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] [Algebra R𝔭 K]
    [IsScalarTower R R𝔭 K] : _root_.IsReduced R𝔭 :=
  isReduced_of_injective (algebraMap R𝔭 K) (algebraMap_P_injective (R := R) (𝔭 := 𝔭) (K := K) R𝔭)

/-- `Spec K → Spec R_𝔭` is scheme-theoretically dominant. -/
theorem isSTD_k : IsSchemeTheoreticallyDominant
    (Spec.map (CommRingCat.ofHom (algebraMap R𝔭 K))) := by
  haveI := isReduced_P (R := R) (𝔭 := 𝔭) R𝔭 K
  haveI : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap R𝔭 K))) := by
    rw [isDominant_iff, Spec.map_base]
    show DenseRange (PrimeSpectrum.comap (algebraMap R𝔭 K))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical]
    intro x hx
    rw [RingHom.mem_ker] at hx
    rw [(algebraMap_P_injective (R := R) (𝔭 := 𝔭) (K := K) R𝔭) (hx.trans (map_zero _).symm)]
    exact zero_mem _
  exact IsSchemeTheoreticallyDominant.of_isDominant _

/-- **Uniqueness.** Two `R`-morphisms from a smooth `R_𝔭`-scheme `W` to a separated `R`-scheme that agree on
the generic fibre `W_K` are equal. -/
theorem uq (X : Over (Spec (CommRingCat.of R))) [IsSeparated X.hom]
    {W : Scheme.{0}} (w : W ⟶ Spec (CommRingCat.of R𝔭)) [Smooth w]
    {P : Scheme.{0}} (p : P ⟶ W) (q : P ⟶ Spec (CommRingCat.of K))
    (H : IsPullback p q w (Spec.map (CommRingCat.ofHom (algebraMap R𝔭 K))))
    (g₁ g₂ : W ⟶ X.left)
    (h₁ : g₁ ≫ X.hom = w ≫ Spec.map (CommRingCat.ofHom (algebraMap R R𝔭)))
    (h₂ : g₂ ≫ X.hom = w ≫ Spec.map (CommRingCat.ofHom (algebraMap R R𝔭)))
    (h : p ≫ g₁ = p ≫ g₂) : g₁ = g₂ := by
  haveI := isSTD_k (R := R) (𝔭 := 𝔭) (K := K) R𝔭
  haveI : Smooth q := MorphismProperty.of_isPullback H ‹Smooth w›
  haveI : IsReduced P := isReduced_of_smooth_field q
  haveI : IsSchemeTheoreticallyDominant p := IsSchemeTheoreticallyDominant.of_isPullback H.flip
  haveI : QuasiCompact p := MorphismProperty.of_isPullback H.flip inferInstance
  haveI : IsReduced W := IsSchemeTheoreticallyDominant.isReduced p
  exact ext_of_isDominant_of_isSeparated X.hom (h₁.trans h₂.symm) p h

omit [IsFractionRing R K] [Algebra R R𝔭] [IsLocalization.AtPrime R𝔭 𝔭] [Algebra R𝔭 K]
  [IsScalarTower R R𝔭 K] in
/-- The Néron property of `X` over `R`, against an arbitrary pullback square for the generic fibre. -/
theorem neron_ext {X : Over (Spec (CommRingCat.of R))} (hX : IsNeronModelOver R K X)
    (Y : Over (Spec (CommRingCat.of R))) [Smooth Y.hom] {P : Scheme.{0}} (p : P ⟶ Y.left)
    (q : P ⟶ Spec (CommRingCat.of K))
    (H : IsPullback p q Y.hom (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (b : P ⟶ X.left) (hb : b ≫ X.hom = q ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    ∃ f : Y.left ⟶ X.left, f ≫ X.hom = Y.hom ∧ p ≫ f = b := by
  have hb' : (H.isoPullback.inv ≫ b) ≫ X.hom =
      pullback.snd Y.hom (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
    rw [Category.assoc, hb, ← Category.assoc, IsPullback.isoPullback_inv_snd]
  let h : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj Y ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj X :=
    Over.homMk (pullback.lift _ _ hb') (pullback.lift_snd _ _ _)
  obtain ⟨f, hf⟩ := (hX.2.2.2.2 Y).2 h
  refine ⟨f.left, Over.w f, ?_⟩
  have h1 := congrArg (fun t => t.left ≫ pullback.fst X.hom
    (Spec.map (CommRingCat.ofHom (algebraMap R K)))) hf
  simp only [Over.pullback_map_left, pullback.lift_fst, h, Over.homMk_left] at h1
  have h2 := congrArg (fun t => H.isoPullback.hom ≫ t) h1
  simp only [IsPullback.isoPullback_hom_fst_assoc, Iso.hom_inv_id_assoc] at h2
  exact h2

/-- **Local existence.** For a smooth affine `R_𝔭`-scheme `V`, an `R`-morphism `V_K → X` extends to `V`. -/
theorem local_ext {X : Over (Spec (CommRingCat.of R))} (hX : IsNeronModelOver R K X)
    (V : Scheme.{0}) [IsAffine V] (v : V ⟶ Spec (CommRingCat.of R𝔭)) [Smooth v]
    (b : pullback v (Spec.map (CommRingCat.ofHom (algebraMap R𝔭 K))) ⟶ X.left)
    (hb : b ≫ X.hom = pullback.snd v (Spec.map (CommRingCat.ofHom (algebraMap R𝔭 K))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    ∃ g : V ⟶ X.left, g ≫ X.hom = v ≫ Spec.map (CommRingCat.ofHom (algebraMap R R𝔭)) ∧
      pullback.fst v (Spec.map (CommRingCat.ofHom (algebraMap R𝔭 K))) ≫ g = b := by
  obtain ⟨a, W, φ, hW, Hφ⟩ := exists_spread (𝔭 := 𝔭) R𝔭 V v
  haveI := hW
  have Hφ' : IsPullback φ v W.hom (Spec.map (CommRingCat.ofHom (toP R𝔭 a.unop))) := Hφ
  let V0 : Over (Spec (CommRingCat.of R)) := Over.mk (W.hom ≫ ej a)
  haveI : Smooth V0.hom := show Smooth (W.hom ≫ ej a) from inferInstance
  have hk : Spec.map (CommRingCat.ofHom (algebraMap R𝔭 K)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R R𝔭)) = Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have H1 := IsPullback.of_hasPullback v (Spec.map (CommRingCat.ofHom (algebraMap R𝔭 K)))
  have H2 := H1.paste_horiz Hφ'
  have H3 : IsPullback (𝟙 W.left) W.hom (W.hom ≫ ej a) (ej a) :=
    IsPullback.of_horiz_isIso_mono ⟨by rw [Category.id_comp]⟩
  have H4 := H2.paste_horiz H3
  have H5 : IsPullback (pullback.fst v (Spec.map (CommRingCat.ofHom (algebraMap R𝔭 K))) ≫ φ)
      (pullback.snd v (Spec.map (CommRingCat.ofHom (algebraMap R𝔭 K)))) V0.hom
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
    have e1 : (Spec.map (CommRingCat.ofHom (algebraMap R𝔭 K)) ≫
        Spec.map (CommRingCat.ofHom (toP R𝔭 a.unop))) ≫ ej a =
        Spec.map (CommRingCat.ofHom (algebraMap R K)) :=
      (Category.assoc _ _ _).trans ((congrArg (fun t => Spec.map (CommRingCat.ofHom (algebraMap R𝔭 K)) ≫ t)
        (toP_ej R𝔭 a)).trans hk)
    rw [Category.comp_id] at H4
    rw [← e1]
    exact H4
  obtain ⟨f0, hf0, hpf⟩ := neron_ext (𝔭 := 𝔭) hX V0 _ _ H5 b hb
  refine ⟨φ ≫ f0, ?_, by rw [← Category.assoc]; exact hpf⟩
  rw [Category.assoc, hf0]
  show φ ≫ W.hom ≫ ej a = _
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ ej a) Hφ'.w).trans
    ((Category.assoc _ _ _).trans (congrArg (v ≫ ·) (toP_ej R𝔭 a))))

/-- **Existence and uniqueness of extensions** for an arbitrary smooth `R_𝔭`-scheme `Y` (local existence on
the affine cover, glued by `uq`). -/
theorem glue_ext {X : Over (Spec (CommRingCat.of R))} [IsSeparated X.hom] (hX : IsNeronModelOver R K X)
    (Y : Scheme.{0}) (y : Y ⟶ Spec (CommRingCat.of R𝔭)) [Smooth y]
    (b : pullback y (Spec.map (CommRingCat.ofHom (algebraMap R𝔭 K))) ⟶ X.left)
    (hb : b ≫ X.hom = pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R𝔭 K))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    ∃ g : Y ⟶ X.left, g ≫ X.hom = y ≫ Spec.map (CommRingCat.ofHom (algebraMap R R𝔭)) ∧
      pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap R𝔭 K))) ≫ g = b := by
  let kK := Spec.map (CommRingCat.ofHom (algebraMap R𝔭 K))
  let 𝒰 := Y.affineCover
  let m : ∀ i, pullback (𝒰.f i ≫ y) kK ⟶ pullback y kK := fun i =>
    pullback.lift (pullback.fst _ _ ≫ 𝒰.f i) (pullback.snd _ _)
      (by rw [Category.assoc]; exact pullback.condition)
  have hm : ∀ i, (m i ≫ b) ≫ X.hom = pullback.snd (𝒰.f i ≫ y) kK ≫
      Spec.map (CommRingCat.ofHom (algebraMap R K)) := fun i => by
    rw [Category.assoc, hb, ← Category.assoc, pullback.lift_snd]
  have hloc := fun i => local_ext (𝔭 := 𝔭) R𝔭 hX (𝒰.X i) (𝒰.f i ≫ y) (m i ≫ b) (hm i)
  choose g hg1 hg2 using hloc
  have compat : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ g i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ g j := by
    intro i j
    let w := pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ y
    have hw' : pullback.snd (𝒰.f i) (𝒰.f j) ≫ 𝒰.f j ≫ y = w := by
      simp only [w, ← Category.assoc, pullback.condition]
    let n : pullback w kK ⟶ pullback (𝒰.f i ≫ y) kK :=
      pullback.lift (pullback.fst w kK ≫ pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.snd w kK)
        (by rw [Category.assoc]; exact pullback.condition)
    let n' : pullback w kK ⟶ pullback (𝒰.f j ≫ y) kK :=
      pullback.lift (pullback.fst w kK ≫ pullback.snd (𝒰.f i) (𝒰.f j)) (pullback.snd w kK)
        (by rw [Category.assoc, hw']; exact pullback.condition)
    have hnn : n ≫ m i = n' ≫ m j := by
      apply pullback.hom_ext
      · simp only [n, n', m, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
        rw [pullback.condition]
      · simp only [n, n', m, Category.assoc, pullback.lift_snd]
    refine uq (𝔭 := 𝔭) R𝔭 X w (pullback.fst w kK) (pullback.snd w kK)
      (IsPullback.of_hasPullback _ _) _ _ ?_ ?_ ?_
    · rw [Category.assoc, hg1 i]
      simp only [w, Category.assoc]
    · rw [Category.assoc, hg1 j, ← hw']
      simp only [Category.assoc]
    · have e1 : pullback.fst w kK ≫ pullback.fst (𝒰.f i) (𝒰.f j) ≫ g i = n ≫ m i ≫ b := by
        rw [← hg2 i, ← Category.assoc, ← Category.assoc, pullback.lift_fst, Category.assoc]
      have e2 : pullback.fst w kK ≫ pullback.snd (𝒰.f i) (𝒰.f j) ≫ g j = n' ≫ m j ≫ b := by
        rw [← hg2 j, ← Category.assoc, ← Category.assoc, pullback.lift_fst, Category.assoc]
      rw [e1, e2, ← Category.assoc, hnn, Category.assoc]
  refine ⟨𝒰.glueMorphisms g compat, ?_, ?_⟩
  · refine Scheme.Cover.hom_ext 𝒰 _ _ (fun i => ?_)
    rw [← Category.assoc, Scheme.Cover.ι_glueMorphisms, hg1 i, Category.assoc]
  · refine Scheme.Cover.hom_ext (𝒰.pullback₁ (pullback.fst y kK)) _ _ (fun (i : 𝒰.I₀) => ?_)
    let F1 := pullback.fst (pullback.fst y kK) (𝒰.f i)
    let F2 := pullback.snd (pullback.fst y kK) (𝒰.f i)
    have hF : F1 ≫ pullback.fst y kK = F2 ≫ 𝒰.f i := pullback.condition
    let ψ : pullback (pullback.fst y kK) (𝒰.f i) ⟶ pullback (𝒰.f i ≫ y) kK :=
      pullback.lift F2 (F1 ≫ pullback.snd y kK)
        (by rw [← Category.assoc, ← hF, Category.assoc, pullback.condition, Category.assoc])
    have hψ : ψ ≫ m i = F1 := by
      apply pullback.hom_ext
      · simp only [ψ, m, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
        exact hF.symm
      · simp only [ψ, m, Category.assoc, pullback.lift_snd]
    show F1 ≫ pullback.fst y kK ≫ 𝒰.glueMorphisms g compat = F1 ≫ b
    rw [← Category.assoc, hF, Category.assoc, Scheme.Cover.ι_glueMorphisms, ← hψ, Category.assoc,
      ← hg2 i, ← Category.assoc, pullback.lift_fst]

/-- **A Néron model over `R` stays a Néron model over `R_𝔭`** (any ring `R` with fraction field `K`, any prime
`𝔭`). -/
theorem isNeronModelOver_localization {X : Over (Spec (CommRingCat.of R))} (hX : IsNeronModelOver R K X) :
    IsNeronModelOver R𝔭 K ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R R𝔭)))).obj X) := by
  have hX' := hX
  obtain ⟨hsm, hsep, hlft, hqc, -⟩ := hX'
  let jR := Spec.map (CommRingCat.ofHom (algebraMap R R𝔭))
  let kK := Spec.map (CommRingCat.ofHom (algebraMap R𝔭 K))
  have hk : kK ≫ jR = Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  refine ⟨show Smooth (pullback.snd X.hom jR) from inferInstance,
    show IsSeparated (pullback.snd X.hom jR) from inferInstance,
    show LocallyOfFiniteType (pullback.snd X.hom jR) from inferInstance,
    show QuasiCompact (pullback.snd X.hom jR) from inferInstance, fun Y _ => ⟨?_, ?_⟩⟩
  · intro f₁ f₂ h
    have w₁ : f₁.left ≫ pullback.snd X.hom jR = Y.hom := Over.w f₁
    have w₂ : f₂.left ≫ pullback.snd X.hom jR = Y.hom := Over.w f₂
    have key : f₁.left ≫ pullback.fst X.hom jR = f₂.left ≫ pullback.fst X.hom jR := by
      refine uq (𝔭 := 𝔭) R𝔭 X Y.hom (pullback.fst Y.hom kK) (pullback.snd Y.hom kK)
        (IsPullback.of_hasPullback _ _) _ _ ?_ ?_ ?_
      · rw [Category.assoc, pullback.condition, ← Category.assoc, w₁]
      · rw [Category.assoc, pullback.condition, ← Category.assoc, w₂]
      · have h1 := congrArg (fun t => t.left ≫ pullback.fst _ _ ≫ pullback.fst _ _) h
        simpa only [Over.pullback_map_left, pullback.lift_fst_assoc, Category.assoc] using h1
    apply Over.OverMorphism.ext
    exact pullback.hom_ext key (w₁.trans w₂.symm)
  · intro h
    have hw : h.left ≫ pullback.snd (pullback.snd X.hom jR) kK = pullback.snd Y.hom kK := Over.w h
    let a := h.left ≫ pullback.fst (pullback.snd X.hom jR) kK ≫ pullback.fst X.hom jR
    have ha : a ≫ X.hom = pullback.snd Y.hom kK ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
      simp only [a, Category.assoc]
      rw [pullback.condition, pullback.condition_assoc, ← Category.assoc, hw, hk]
    obtain ⟨g, hg1, hg2⟩ := glue_ext (𝔭 := 𝔭) R𝔭 hX Y.left Y.hom a ha
    refine ⟨Over.homMk (pullback.lift g Y.hom hg1) (pullback.lift_snd _ _ _), ?_⟩
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [Over.pullback_map_left, Over.homMk_left, Category.assoc, pullback.lift_fst]
        exact hg2
      · simp only [Over.pullback_map_left, Over.homMk_left, Category.assoc, pullback.lift_fst,
          pullback.lift_snd]
        exact pullback.condition.trans ((congrArg (· ≫ kK) hw).symm.trans ((Category.assoc _ _ _).trans
          (congrArg (h.left ≫ ·) pullback.condition.symm)))
    · simp only [Over.pullback_map_left, Over.homMk_left, pullback.lift_snd]
      exact hw.symm

end Main

/-! ## The `.mp` half of BLR 1.2/4 -/

/-- **The `.mp` half of `CToPrinted.BLR_1_2_4`** (BLR, *Néron models*, §1.2 Prop. 4, "only if"), stated with the
same binders. -/
def BLR_1_2_4_MP : Prop :=
  ∀ (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (X : Over (Spec (CommRingCat.of R))) [Smooth X.hom] [IsSeparated X.hom] [QuasiCompact X.hom],
    IsNeronModelOver R K X →
      ∀ (𝔭 : Ideal R) [𝔭.IsMaximal] (R𝔭 : Type) [CommRing R𝔭] [Algebra R R𝔭]
        [IsLocalization.AtPrime R𝔭 𝔭] [Algebra R𝔭 K] [IsScalarTower R R𝔭 K],
        IsNeronModelOver R𝔭 K ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R R𝔭)))).obj X)

/-- **`BLR_1_2_4_MP`, proved.** -/
theorem blr_1_2_4_mp : BLR_1_2_4_MP := by
  intro R K _ _ _ _ _ X _ _ _ hX 𝔭 _ R𝔭 _ _ _ _ _
  exact isNeronModelOver_localization (𝔭 := 𝔭) R𝔭 hX

end GapBLR

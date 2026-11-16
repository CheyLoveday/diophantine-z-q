import ZInQKernel.Contrib.OneProof.NeronExtSpread

/-! # neron-ext: a Néron model near a closed point from a Néron model over its local ring -/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry
open NumberField

namespace NeronExt

open GapBLR ZInQ.Contrib.SpreadOut

section Gen

theorem isPullback_id_mono {C : Type*} [Category C] {W D Z : C} (g : W ⟶ D) (m : D ⟶ Z) [Mono m] :
    IsPullback (𝟙 W) g (g ≫ m) m := by
  refine IsPullback.of_isLimit' ⟨by simp⟩ (PullbackCone.IsLimit.mk _ (fun s => s.fst) (fun s => ?_)
    (fun s => ?_) (fun s l h1 h2 => ?_))
  · simp
  · rw [← cancel_mono m]; simpa using s.condition
  · simpa using h1

/-- For a monomorphism `m`, pulling `W → D → Z` back along `m` gives `W`. -/
noncomputable def pbMapIso {Z D : Scheme.{0}} (m : D ⟶ Z) [Mono m] (W : Over D) :
    (Over.pullback m).obj (Over.mk (W.hom ≫ m)) ≅ W :=
  Over.isoMk ((isPullback_id_mono W.hom m).isoPullback.symm) (by
    show (isPullback_id_mono W.hom m).isoPullback.inv ≫ W.hom = pullback.snd (W.hom ≫ m) m
    exact (isPullback_id_mono W.hom m).isoPullback_inv_snd)

theorem isNeronModelOver_of_iso {R K : Type} [CommRing R] [Field K] [Algebra R K]
    {X X' : Over (Spec (CommRingCat.of R))} (i : X ≅ X')
    (h : CToPrinted.IsNeronModelOver R K X') : CToPrinted.IsNeronModelOver R K X := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hX : X.hom = i.hom.left ≫ X'.hom := (Over.w i.hom).symm
  haveI : IsIso i.hom.left := ⟨i.inv.left, by rw [← Over.comp_left, i.hom_inv_id]; rfl,
    by rw [← Over.comp_left, i.inv_hom_id]; rfl⟩
  refine ⟨by rw [hX]; infer_instance, by rw [hX]; infer_instance, by rw [hX]; infer_instance,
    by rw [hX]; infer_instance, fun Y _ => ?_⟩
  let F := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  have hb := h5 Y
  have e : (fun f : Y ⟶ X => F.map f) =
      (fun g => g ≫ (F.mapIso i).inv) ∘ (fun g : Y ⟶ X' => F.map g) ∘ (fun f => f ≫ i.hom) := by
    funext f
    simp only [Function.comp_apply, Functor.mapIso_inv, CategoryTheory.Functor.map_comp,
      Category.assoc, ← CategoryTheory.Functor.map_comp F i.hom i.inv, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.comp_id]
  rw [e]
  have b1 : Function.Bijective (fun f : Y ⟶ X => f ≫ i.hom) :=
    ⟨fun a b hab => by simpa using congrArg (· ≫ i.inv) hab, fun g => ⟨g ≫ i.inv, by simp⟩⟩
  have b2 : Function.Bijective (fun g : F.obj Y ⟶ F.obj X' => g ≫ (F.mapIso i).inv) :=
    ⟨fun a b hab => by simpa using congrArg (· ≫ (F.mapIso i).hom) hab,
      fun g => ⟨g ≫ (F.mapIso i).hom, by simp⟩⟩
  exact b2.comp (hb.comp b1)

variable {L : Type} [Field L] [NumberField L]

theorem locNeron_of_iso {𝔭 : Ideal (𝓞 L)} [𝔭.IsPrime] {X X' : Over (S L)} (i : X ≅ X')
    (h : LocNeron L 𝔭 X') : LocNeron L 𝔭 X := by
  unfold LocNeron at *
  letI := locAlg L 𝔭
  exact isNeronModelOver_of_iso ((Over.pullback _).mapIso i) h

/-- `Spec (𝓞_L)_w → Spec 𝓞_L` lands in every open containing `w`. -/
theorem preimage_loc_eq_top (w : Ideal (𝓞 L)) [w.IsPrime] {U : (S L).Opens} (hw : w ∈ maxIn U) :
    (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (Localization.AtPrime w)))) ⁻¹ᵁ U = ⊤ := by
  obtain ⟨x, hxU, hx⟩ := hw
  refine top_unique (fun q _ => ?_)
  let y : PrimeSpectrum (𝓞 L) := PrimeSpectrum.comap (algebraMap (𝓞 L) (Localization.AtPrime w)) q
  have hy : (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (Localization.AtPrime w)))) q = y := by
    rw [Spec.map_base]; rfl
  have hle : y ≤ x := by
    show Ideal.comap _ q.asIdeal ≤ x.asIdeal
    rw [hx]
    calc Ideal.comap _ q.asIdeal ≤ Ideal.comap (algebraMap (𝓞 L) (Localization.AtPrime w))
          (IsLocalRing.maximalIdeal _) :=
          Ideal.comap_mono (IsLocalRing.le_maximalIdeal q.isPrime.ne_top)
      _ = w := Localization.AtPrime.under_maximalIdeal
  show (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (Localization.AtPrime w)))) q ∈ U
  rw [hy]
  exact ((PrimeSpectrum.le_iff_specializes y x).mp hle).mem_open U.isOpen hxU

theorem isIso_pb_resι {T : Scheme.{0}} (j : T ⟶ S L) (X : Over (S L)) {U : (S L).Opens}
    (hU : j ⁻¹ᵁ U = ⊤) : IsIso ((Over.pullback j).map (resι X U)) :=
  isIso_pb_map j (resι X U) U hU (fun x hx => by
    show x ∈ Set.range (X.hom ⁻¹ᵁ U).ι
    rw [Scheme.Opens.range_ι]; exact hx)

theorem locNeron_res_iff {w : Ideal (𝓞 L)} [w.IsPrime] {U : (S L).Opens} (hw : w ∈ maxIn U)
    (X : Over (S L)) : LocNeron L w (res X U) ↔ LocNeron L w X := by
  haveI := isIso_pb_resι (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (Localization.AtPrime w))))
    X (preimage_loc_eq_top w hw)
  let i := asIso ((Over.pullback (Spec.map (CommRingCat.ofHom
    (algebraMap (𝓞 L) (Localization.AtPrime w))))).map (resι X U))
  unfold LocNeron
  letI := locAlg L w
  exact ⟨fun h => isNeronModelOver_of_iso i.symm h, fun h => isNeronModelOver_of_iso i h⟩

end Gen

section Near

variable {L : Type} [Field L] [NumberField L]

theorem mem_ej_opensRange {𝔭 : Ideal (𝓞 L)} [𝔭.IsPrime] (a : (GapBLR.Idx 𝔭)ᵒᵖ) {x : S L} :
    x ∈ (ej a).opensRange ↔ a.unop.s ∉ (PrimeSpectrum.asIdeal (R := 𝓞 L) x) := by
  have hrange := Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of (𝓞 L)) a.unop.s
  exact (Eq.to_iff (congrArg (x ∈ ·) hrange)).trans (PrimeSpectrum.mem_basicOpen _ _)

/-- The point of `Spec 𝓞_L` of a prime ideal. -/
def pt (v : Ideal (𝓞 L)) [hv : v.IsPrime] : S L := (⟨v, hv⟩ : PrimeSpectrum (𝓞 L))

/-- The Néron property of `N` over `(𝓞_L)_v` (algebra `locAlg`), with `N_L ≅ B`. -/
def LocalModel (B : Over (Spec (CommRingCat.of L))) (v : Ideal (𝓞 L)) [v.IsPrime]
    (N : Over (Spec (CommRingCat.of (Localization.AtPrime v)))) : Prop :=
  letI := locAlg L v
  CToPrinted.IsNeronModelOver (Localization.AtPrime v) L N ∧
    Nonempty ((Over.pullback (Spec.map (CommRingCat.ofHom
      (algebraMap (Localization.AtPrime v) L)))).obj N ≅ B)

/-- **Spreading the local Néron model at `v`.** -/
theorem spreadAt (B : Over (Spec (CommRingCat.of L))) (v : Ideal (𝓞 L)) [v.IsPrime]
    (N : Over (Spec (CommRingCat.of (Localization.AtPrime v)))) (hN : LocalModel B v N) :
    ∃ (Dv : (S L).Opens) (X : Over (S L)) (_ : Smooth X.hom) (_ : IsSeparated X.hom)
      (_ : QuasiCompact X.hom) (_ : (gf L).obj X ≅ B), pt v ∈ Dv ∧ Supp L Dv X ∧ LocNeron L v X := by
  letI := locAlg L v
  haveI := locAlg_tower L v
  obtain ⟨⟨h1, h2, h3, h4, h5⟩, ⟨eN⟩⟩ := hN
  haveI := h1; haveI := h2; haveI := h4
  obtain ⟨a, W, hWs, hWsep, hWqc, ⟨eW⟩⟩ := exists_spread_sep (𝔭 := v) (Localization.AtPrime v) N
  haveI := hWs; haveI := hWsep; haveI := hWqc
  let X : Over (S L) := Over.mk (W.hom ≫ ej a)
  haveI : Smooth X.hom := show Smooth (W.hom ≫ ej a) from inferInstance
  haveI : IsSeparated X.hom := show IsSeparated (W.hom ≫ ej a) from inferInstance
  haveI : QuasiCompact X.hom := show QuasiCompact (W.hom ≫ ej a) from inferInstance
  let jv := Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (Localization.AtPrime v)))
  have hjv : (specCone v (Localization.AtPrime v)).π.app a ≫ ej a = jv := π_ej _ a
  let pbX : (Over.pullback jv).obj X ≅ N :=
    pbCongr hjv.symm X ≪≫ (Over.pullbackComp _ (ej a)).app X ≪≫
      (Over.pullback _).mapIso (pbMapIso (ej a) W) ≪≫ eW
  let kL := Spec.map (CommRingCat.ofHom (algebraMap (Localization.AtPrime v) L))
  have hk : kL ≫ jv = jL L := by
    simp only [kL, jv, jL, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [← IsScalarTower.algebraMap_eq]
  let eX : (gf L).obj X ≅ B :=
    pbCongr hk.symm X ≪≫ (Over.pullbackComp kL jv).app X ≪≫ (Over.pullback kL).mapIso pbX ≪≫ eN
  refine ⟨(ej a).opensRange, X, inferInstance, inferInstance, inferInstance, eX, ?_, ?_, ?_⟩
  · exact (mem_ej_opensRange a).2 a.unop.hs
  · show (W.hom ≫ ej a) ⁻¹ᵁ (ej a).opensRange = ⊤
    rw [Scheme.Hom.comp_preimage, Scheme.Hom.preimage_opensRange, Scheme.Hom.preimage_top]
  · show CToPrinted.IsNeronModelOver (Localization.AtPrime v) L ((Over.pullback jv).obj X)
    exact isNeronModelOver_of_iso pbX ⟨h1, h2, h3, h4, h5⟩

/-- **Prime avoidance.** For `k ≠ 0` and a maximal `v`, some `g ∉ v` lies in every other maximal ideal
containing `k`. -/
theorem exists_avoid (v : Ideal (𝓞 L)) [hv : v.IsMaximal] (k : 𝓞 L) (hk : k ≠ 0) :
    ∃ g : 𝓞 L, g ∉ v ∧ ∀ w : Ideal (𝓞 L), w.IsMaximal → w ≠ v → k ∈ w → g ∈ w := by
  classical
  have hI : Ideal.span {k} ≠ (0 : Ideal (𝓞 L)) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hk
  let T := (Ideal.finite_factors hI).toFinset.filter (fun w => w.asIdeal ≠ v)
  have hx : ∀ w ∈ T, ∃ x ∈ w.asIdeal, x ∉ v := by
    intro w hw
    have hwv : w.asIdeal ≠ v := (Finset.mem_filter.1 hw).2
    by_contra hcon
    push Not at hcon
    have hle : w.asIdeal ≤ v := hcon
    haveI : w.asIdeal.IsMaximal := w.isMaximal
    exact hwv (Ideal.IsMaximal.eq_of_le this hv.ne_top hle)
  choose x hxw hxv using hx
  refine ⟨∏ w ∈ T.attach, x w.1 w.2, ?_, ?_⟩
  · rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨w, -, hw⟩
    exact hxv w.1 w.2 hw
  · intro w hwmax hwv hkw
    have hw0 : w ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hwmax (RingOfIntegers.not_isField L)
    let w' : IsDedekindDomain.HeightOneSpectrum (𝓞 L) := ⟨w, hwmax.isPrime, hw0⟩
    have hw'T : w' ∈ T := by
      refine Finset.mem_filter.2 ⟨?_, hwv⟩
      rw [Set.Finite.mem_toFinset]
      show w ∣ Ideal.span {k}
      rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]; exact hkw
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun u : T => x u.1 u.2) (Finset.mem_attach T ⟨w', hw'T⟩)
    rw [hc]
    exact Ideal.mul_mem_right c _ (hxw w' hw'T)

end Near

end NeronExt

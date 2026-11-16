import ZInQKernel.Contrib.OneProof.GroupLawSpread
import ZInQKernel.OneProof.H.TailZ40

/-!
# group-law: Mumford's group law over a reduced base from the local case

Task group-law (2026-11-16). The research field `mumfordGroupLaw` is `ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw`
(*GIT* Thm 6.14 over any locally noetherian `S`). Its only consumer on the chain is
`LeafQM.AV.R1UnivRigid.qmFamilyGroupLaw_of_groupLaw` (`ZInQKernel/OneProof/H/TailZ40.lean`), i.e. the chain uses it
only over proper smooth curves `S/ℚ` (`QMFamilyGroupLaw`).

This file proves, with no `sorry` and the standard axioms:

* `mumfordGroupLawRed_of_local : MumfordGroupLawLocal → MumfordGroupLawRed`: the group law over every reduced
  locally noetherian `S` (with `F`, `F ×_S F`, `(F ×_S F) ×_S F` reduced) from the group law over the spectra of
  reduced noetherian local rings. Proof: at `s ∈ S` take an affine open `V = Spec A ∋ s` and the prime `𝔭` of `s`;
  the leaf gives the group law on `F ×_S Spec A_𝔭`; it spreads to an open neighbourhood of `s`
  (`GroupLawSpread.localLaw_of_stalk`); the local group laws agree on the field points of the reduced overlaps (they
  are the fibres' group laws, by the chain's field-level rigidity) and glue (`GroupLawGlue.exists_grpObj_of_localLaws`).
* `qmFamilyGroupLaw_of_red : MumfordGroupLawRed → QMFamilyGroupLaw`, hence
  `qmFamilyGroupLaw_of_local : MumfordGroupLawLocal → QMFamilyGroupLaw`: the chain's only use of the field.

The field itself (non-reduced bases included) is **not** proved: over a non-reduced base the local group laws need
not agree on overlaps without a rigidity input over the base, and the local case itself is the deformation-theoretic
core of *GIT* Thm 6.14 (report: docs/research/group-law.md).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

namespace ZInQ.Contrib.GroupLaw

open LeafQM.AV.R1UnivRigid PkgI3

/-- **LEAF (Mumford's Thm 6.14 over a reduced noetherian local base).** Let `R` be a reduced noetherian local ring,
`F → Spec R` proper, smooth, with geometrically connected fibres, `e` a section, every field fibre an abelian variety
with origin `e(s)`. Then `F` carries a group object structure in `Over (Spec R)` with identity `e`.

Source (numbers UNVERIFIED, no network): Mumford–Fogarty–Kirwan, *Geometric Invariant Theory*, 3rd ed., Ch. 6 §1,
Thm 6.14 (`S` connected and locally noetherian, `F → S` smooth and proper with a section `e`, one geometric fibre an
abelian variety: `F` is an abelian scheme with identity `e`; Grothendieck's proof through §6.3). *Form*: the
printed theorem with `S = Spec R` (connected, `R` local; noetherian) and stronger hypotheses (every field fibre an
abelian variety, geometrically connected); the conclusion is the group-object part of "abelian scheme". A consequence
of the field `MumfordGroupLaw` (`local_of_field`), so never stronger than it. -/
def MumfordGroupLawLocal : Prop :=
  ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [_root_.IsReduced R]
    (F : Over (Spec (CommRingCat.of R))) (e : Spec (CommRingCat.of R) ⟶ F.left),
    IsProper F.hom → Smooth F.hom → GeometricallyConnected F.hom → e ≫ F.hom = 𝟙 _ →
    (∀ (K : Type) [Field K] (s : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)),
      ∃ (A : AbVar K) (g : A.X.left ⟶ F.left), IsAbVarFibre F e s A g) →
    ∃ _G : GrpObj F, η[F].left = e

/-- The local leaf is an instance of the field. -/
theorem local_of_field (h : ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw) : MumfordGroupLawLocal :=
  fun R _ _ _ _ F e h1 h2 h3 h4 h5 => h _ F e inferInstance h1 h2 h3 h4 h5

/-- **`MumfordGroupLaw` over a reduced base** (the field with four reducedness hypotheses added): the form the chain
uses (`qmFamilyGroupLaw_of_red`). -/
def MumfordGroupLawRed : Prop :=
  ∀ (S : Scheme.{0}) (F : Over S) (e : S ⟶ F.left), IsLocallyNoetherian S → IsReduced S →
    IsReduced F.left → IsReduced (F ⊗ F).left → IsReduced ((F ⊗ F) ⊗ F).left →
    IsProper F.hom → Smooth F.hom → GeometricallyConnected F.hom → e ≫ F.hom = 𝟙 S →
    (∀ (K : Type) [Field K] (s : Spec (CommRingCat.of K) ⟶ S),
      ∃ (A : AbVar K) (g : A.X.left ⟶ F.left), IsAbVarFibre F e s A g) →
    ∃ _G : GrpObj F, η[F].left = e

/-- The reduced form is implied by the field (it only adds hypotheses). -/
theorem red_of_field (h : ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw) : MumfordGroupLawRed :=
  fun S F e h0 _ _ _ _ h1 h2 h3 h4 h5 => h S F e h0 h1 h2 h3 h4 h5

/-- **The group law over a reduced base from the local leaf.** -/
theorem mumfordGroupLawRed_of_local (hL : MumfordGroupLawLocal) : MumfordGroupLawRed := by
  intro S F e hN hRS hRF hRFF hRFFF hP hSm hGC he hfib
  haveI := hP
  haveI := hSm
  haveI := hGC
  have hloc : ∀ s : S, ∃ L : LocalLaw F e, s ∈ Set.range L.j := by
    intro s
    obtain ⟨V, hV, hsV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := s) trivial
    let x : V := ⟨s, hsV⟩
    let 𝔭 := (hV.primeIdealOf x).asIdeal
    haveI : IsNoetherianRing Γ(S, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
    haveI : IsNoetherianRing (Localization.AtPrime 𝔭) :=
      IsLocalization.isNoetherianRing 𝔭.primeCompl _ inferInstance
    haveI : _root_.IsReduced (Localization.AtPrime 𝔭) :=
      isReduced_localizationPreserves 𝔭.primeCompl (Localization.AtPrime 𝔭) inferInstance
    let J := locMap hV 𝔭
    let N := (Over.pullback J).obj F
    let eN : Spec (CommRingCat.of (Localization.AtPrime 𝔭)) ⟶ N.left :=
      pullback.lift (J ≫ e) (𝟙 _) (by rw [Category.assoc, he, Category.comp_id, Category.id_comp])
    have heN : eN ≫ N.hom = 𝟙 _ := pullback.lift_snd _ _ _
    have heNq : eN ≫ pullback.fst F.hom J = J ≫ e := pullback.lift_fst _ _ _
    have hfibN := fibreHyp_of_isPullback (IsPullback.of_hasPullback F.hom J) heN heNq hfib
    obtain ⟨G, hη⟩ := hL (Localization.AtPrime 𝔭) N eN
      (by change IsProper (pullback.snd F.hom J); infer_instance)
      (by change Smooth (pullback.snd F.hom J); infer_instance)
      (by change GeometricallyConnected (pullback.snd F.hom J); infer_instance)
      heN hfibN
    obtain ⟨L, hL⟩ := localLaw_of_stalk hV 𝔭 he G (by rw [hη]; exact heNq)
    refine ⟨L, ?_⟩
    have : hV.fromSpec (⟨𝔭, inferInstance⟩ : PrimeSpectrum Γ(S, V)) = s :=
      hV.fromSpec_primeIdealOf x
    rw [← this]
    exact hL
  choose L hL using hloc
  exact exists_grpObj_of_localLaws L hL he hfib

end ZInQ.Contrib.GroupLaw

namespace LeafQM

namespace AV

namespace R1UnivRigid

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3 ZInQ.Contrib.GroupLaw

/-- rigid-prune's `exists_qmAbScheme_gl` (verbatim), from the reduced-base form `MumfordGroupLawRed`. -/
theorem exists_qmAbScheme_red (hG : MumfordGroupLawRed) {S : Scheme.{0}}
    [IsReduced S] [IsLocallyNoetherian S] (𝒜 : QMFamily S) [IsReduced 𝒜.F.left]
    [IsReduced (𝒜.F ⊗ 𝒜.F).left] [IsReduced ((𝒜.F ⊗ 𝒜.F) ⊗ 𝒜.F).left]
    (hfib : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ S), ∃ P : QML3 K,
      IsFibreOf 𝒜 t P) :
    ∃ 𝒜' : QMAbScheme S, 𝒜'.toQMFamily = 𝒜 := by
  have := 𝒜.proper
  have := 𝒜.smooth
  have hsm : Smooth 𝒜.F.hom := SmoothOfRelativeDimension.smooth 2 _
  have hgc := geomConn_of_fibres 𝒜 hfib
  obtain ⟨G, hη⟩ := hG S 𝒜.F (𝒜.eta 0) inferInstance inferInstance inferInstance inferInstance
    inferInstance 𝒜.proper hsm hgc (𝒜.eta_sec 0)
    (fun K _ s => by
      obtain ⟨P, g, hpb, -, he⟩ := hfib K s
      exact ⟨P.A, g, hpb, one_left_comp he⟩)
  have hb : ∀ (K : Type) [Field K] (s : Spec (CommRingCat.of K) ⟶ S) (A : AbVar K)
      (g : A.X.left ⟶ 𝒜.F.left), IsAbVarFibre 𝒜.F (𝒜.eta 0) s A g → IsGrpFibre 𝒜.F A g :=
    fun K _ s A g h => isGrpFibre_of_rigidity 𝒜.F s A g (by rw [hη]; exact h)
  -- `η(0)` is fixed by every `ι(a)`
  have hιe : ∀ a : O, 𝒜.eta 0 ≫ 𝒜.iota a = 𝒜.eta 0 := fun a => by
    refine sec_ext 𝒜 hfib _ _ (by rw [Category.assoc, 𝒜.iota_over])
      (fun K _ t P g hpb hι he => ?_)
    have h0 : t ≫ 𝒜.eta 0 = (1 : P.A.Pt K).left ≫ g := (one_left_comp he).symm
    rw [← Category.assoc t, h0]
    erw [Category.assoc, ← hι a, ← Over.comp_left_assoc, MonObj.one_comp]
  have hone : 𝒜.iota 1 = 𝟙 _ := F_ext 𝒜 hfib _ _ (by rw [𝒜.iota_over, Category.id_comp])
    (fun K _ t P g hpb hι he => by
      rw [← hι 1, map_one, Category.comp_id]
      show (𝟙 P.A.X : P.A.X ⟶ P.A.X).left ≫ g = g
      simp)
  have hmul : ∀ a b : O, 𝒜.iota (a * b) = 𝒜.iota b ≫ 𝒜.iota a := fun a b =>
    F_ext 𝒜 hfib _ _ (by rw [𝒜.iota_over, Category.assoc, 𝒜.iota_over, 𝒜.iota_over])
      (fun K _ t P g hpb hι he => by
        rw [← Category.assoc g (𝒜.iota b), ← hι b, Category.assoc, ← hι a, ← hι (a * b), map_mul]
        show ((P.q.iota b).hom ≫ (P.q.iota a).hom).left ≫ g = _
        rw [Over.comp_left, Category.assoc])
  have hadd : ∀ a b : O, (Over.homMk (𝒜.iota (a + b)) (𝒜.iota_over _) : 𝒜.F ⟶ 𝒜.F) =
      Over.homMk (𝒜.iota a) (𝒜.iota_over a) * Over.homMk (𝒜.iota b) (𝒜.iota_over b) :=
    fun a b => by
      apply Over.OverMorphism.ext
      refine F_ext 𝒜 hfib _ _ (by rw [Over.w, Over.w])
        (fun K _ t P g hpb hι he => ?_)
      obtain ⟨φ, hφ₁, hφ₂, hφμ⟩ := hb K t P.A g ⟨hpb, one_left_comp he⟩
      change g ≫ 𝒜.iota (a + b) = _
      rw [← hι (a + b), map_add, AbVar.Hom.hom_add,
        CategoryTheory.Hom.mul_def, CategoryTheory.Hom.mul_def, Over.comp_left, Over.comp_left,
        Category.assoc, hφμ,
        reassoc_of% (lift_comp_φ _ _ (Over.homMk (𝒜.iota a) (𝒜.iota_over a) : 𝒜.F ⟶ 𝒜.F)
          (Over.homMk (𝒜.iota b) (𝒜.iota_over b)) g φ hφ₁ hφ₂ (hι a) (hι b))]
  have headd : ∀ a b : O,
      (Over.homMk (U := 𝟙_ (Over S)) (𝒜.eta (a + b)) (𝒜.eta_sec _) : 𝟙_ (Over S) ⟶ 𝒜.F) =
      Over.homMk (U := 𝟙_ (Over S)) (𝒜.eta a) (𝒜.eta_sec a) *
        Over.homMk (U := 𝟙_ (Over S)) (𝒜.eta b) (𝒜.eta_sec b) := fun a b => by
    apply Over.OverMorphism.ext
    refine sec_ext 𝒜 hfib _ _ (by rw [Over.w, Over.w])
      (fun K _ t P g hpb hι he => ?_)
    obtain ⟨φ, hφ₁, hφ₂, hφμ⟩ := hb K t P.A g ⟨hpb, one_left_comp he⟩
    change t ≫ 𝒜.eta (a + b) = _
    rw [← he (a + b), map_add, toMul_add,
      CategoryTheory.Hom.mul_def, CategoryTheory.Hom.mul_def, Over.comp_left, Over.comp_left,
      Category.assoc, hφμ,
      reassoc_of% (lift_comp_φ _ _ (Over.homMk (U := 𝟙_ (Over S)) (𝒜.eta a) (𝒜.eta_sec a))
        (Over.homMk (U := 𝟙_ (Over S)) (𝒜.eta b) (𝒜.eta_sec b)) t φ hφ₁ hφ₂ (he a) (he b))]
    rfl
  have helin : ∀ a b : O, 𝒜.eta (a * b) = 𝒜.eta b ≫ 𝒜.iota a := fun a b => by
    refine sec_ext 𝒜 hfib _ _
      (by rw [𝒜.eta_sec, Category.assoc, 𝒜.iota_over, 𝒜.eta_sec])
      (fun K _ t P g hpb hι he => ?_)
    have hl : Additive.toMul (P.e.eta (a * b)) =
        Additive.toMul (P.e.eta b) ≫ (P.q.iota a).hom := by
      rw [P.e.linear]; rfl
    rw [← he (a * b), hl, Over.comp_left, Category.assoc, hι a, reassoc_of% (he b)]
    rfl
  have hthree : ∀ b : O, 𝒜.eta (3 * b) = 𝒜.eta 0 := fun b =>
    sec_ext 𝒜 hfib _ _ (by rw [𝒜.eta_sec, 𝒜.eta_sec]) (fun K _ t P g hpb hι he => by
      rw [← he (3 * b), ← he 0, (P.e.eq_iff (3 * b) 0).2 ⟨b, by simp⟩])
  have hker : ∀ (K : Type) [Field K] (s : Spec (CommRingCat.of K) ⟶ S) (a : O),
      s ≫ 𝒜.eta a = s ≫ 𝒜.eta 0 ↔ ∃ b : O, a = 3 * b := by
    intro K _ s a
    obtain ⟨P, g, hpb, hι, he⟩ := hfib K s
    rw [← he a, ← he 0]
    constructor
    · intro h
      have h' : Additive.toMul (P.e.eta a) = Additive.toMul (P.e.eta 0) := by
        apply Over.OverMorphism.ext
        apply hpb.hom_ext h
        rw [Over.w, Over.w]
      obtain ⟨c, hc⟩ := (P.e.eq_iff a 0).1 (Additive.toMul.injective h')
      exact ⟨c, by simpa using hc⟩
    · rintro ⟨b, rfl⟩
      rw [(P.e.eq_iff (3 * b) 0).2 ⟨b, by simp⟩]
  refine ⟨{ 𝒜 with
    grp := G
    geomConn := hgc
    one_eq := hη
    iota_hom := fun a => isMonHom_of_fibres 𝒜 hη hfib a (hιe a)
    iota_one := hone
    iota_mul := hmul
    iota_add := hadd
    eta_add := headd
    eta_linear := helin
    eta_three := hthree
    eta_ker := hker }, rfl⟩

/-- **`QMFamilyGroupLaw` from the reduced-base form `MumfordGroupLawRed`** (rigid-prune's `qmFamilyGroupLaw_of_groupLaw`,
verbatim, with `(F ×_S F) ×_S F` smooth over `ℚ`, hence reduced, added). -/
theorem qmFamilyGroupLaw_of_red (hG : MumfordGroupLawRed) :
    QMFamilyGroupLaw := by
  intro S _ hs 𝒜 hfib
  obtain ⟨h1, h2, h3⟩ := reduced_of_smooth_curve hs 𝒜
  have : Smooth S.hom := SmoothOfRelativeDimension.smooth 1 _
  have := 𝒜.smooth
  have : Smooth 𝒜.F.hom := SmoothOfRelativeDimension.smooth 2 _
  have : Smooth (𝒜.F ⊗ 𝒜.F).hom := by
    rw [Over.tensorObj_hom]
    infer_instance
  have : IsReduced (𝒜.F ⊗ 𝒜.F).left := isReduced_of_smooth ((𝒜.F ⊗ 𝒜.F).hom ≫ S.hom)
  have : Smooth ((𝒜.F ⊗ 𝒜.F) ⊗ 𝒜.F).hom := by
    rw [Over.tensorObj_hom]
    infer_instance
  have : IsReduced ((𝒜.F ⊗ 𝒜.F) ⊗ 𝒜.F).left :=
    isReduced_of_smooth (((𝒜.F ⊗ 𝒜.F) ⊗ 𝒜.F).hom ≫ S.hom)
  exact exists_qmAbScheme_red hG 𝒜 (fun K _ t => fibre_of_fieldPt 𝒜 hfib t)

/-- **`QMFamilyGroupLaw` (the chain's only use of the field `mumfordGroupLaw`) from the local leaf.** -/
theorem qmFamilyGroupLaw_of_local (hL : MumfordGroupLawLocal) : QMFamilyGroupLaw :=
  qmFamilyGroupLaw_of_red (mumfordGroupLawRed_of_local hL)

end R1UnivRigid

end AV

end LeafQM

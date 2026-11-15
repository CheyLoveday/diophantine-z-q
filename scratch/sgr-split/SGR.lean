import ZInQKernel.OneProof.H.TailW
import ZInQKernel.OneProof.H.TailZ16

/-! sgr-split: `HDec.CurveSplitGR.ShimuraGoodReductionNoGuard` from the printed representability of the
integral moduli problem of QM abelian surfaces with level 3 (on the kernel's `QMAbScheme`). -/

noncomputable section

namespace HDec.SGRSplit

open CategoryTheory AlgebraicGeometry Limits
open _root_.LeafQM _root_.LeafQM.AV _root_.LeafQM.AV.R1UnivRigid VertWitness CurveSplitGR

/-- **`𝒜'` is the pullback of `𝒜` along `g`, with its `𝒪`-action and level sections**: a morphism
`h : 𝒜' → 𝒜` making `𝒜' → S` the base change of `𝒜 → T` along `g`, carrying `ι'(a)` to `ι(a)` and
`η'(a)` to `η(a)`; i.e. an isomorphism `𝒜' ≅ g^*𝒜` of `QMFamily`s (the relative form of `IsFibreOf`). -/
def QMFamFibre {S T : Scheme.{0}} (𝒜 : QMFamily T) (g : S ⟶ T) (𝒜' : QMFamily S) : Prop :=
  ∃ h : 𝒜'.F.left ⟶ 𝒜.F.left, IsPullback h 𝒜'.F.hom 𝒜.F.hom g ∧
    (∀ a : O, 𝒜'.iota a ≫ h = h ≫ 𝒜.iota a) ∧ (∀ a : O, 𝒜'.eta a ≫ h = g ≫ 𝒜.eta a)

/-- Representability at `p` (see `ShimuraIntegralModelRep`). -/
def ShimuraIntegralModelRepAt (p : ℕ) [Fact p.Prime] : Prop :=
  ∃ (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))) (𝒜 : QMAbScheme 𝒴.left),
    IsProper 𝒴.hom ∧ SmoothOfRelativeDimension 1 𝒴.hom ∧
    ∀ (S : Over (Spec (CommRingCat.of (Zloc p)))), IsLocallyNoetherian S.left →
      ∀ 𝒜' : QMAbScheme S.left, ∃! g : S ⟶ 𝒴, QMFamFibre 𝒜.toQMFamily g.left 𝒜'.toQMFamily

/-- placeholder docstring (see the final file). -/
def ShimuraIntegralModelRep : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 324 < p → ShimuraIntegralModelRepAt p

/-- Glue G1. -/
def QMAbFieldFibre : Prop :=
  ∀ (S : Scheme.{0}) (𝒜 : QMAbScheme S) (K : Type) [Field K] [Algebra ℚ K]
    (y : Spec (CommRingCat.of K) ⟶ S), ∃ P : QML3 K, IsFibreOf 𝒜.toQMFamily y P

/-- Glue G2. -/
def QML3AsQMAb : Prop :=
  ∀ (K : Type) [Field K] [Algebra ℚ K] (P : QML3 K), ∃ 𝒜' : QMAbScheme (Spec (CommRingCat.of K)),
    ∀ (T : Scheme.{0}) (𝒜 : QMFamily T) (y : Spec (CommRingCat.of K) ⟶ T),
      IsFibreOf 𝒜 y P ↔ QMFamFibre 𝒜 y 𝒜'.toQMFamily

/-- Glue G3. -/
def FibreClassUnique : Prop :=
  ∀ (S : Scheme.{0}) (𝒜 : QMFamily S) (K : Type) [Field K] (y : Spec (CommRingCat.of K) ⟶ S)
    (P P' : QML3 K), IsFibreOf 𝒜 y P → IsFibreOf 𝒜 y P' → M3.mk P = M3.mk P'

/-! ## Lemmas -/

/-- Morphisms `Spec R → Spec ℤ_(p)` are unique. -/
theorem spec_to_Zloc_ext (p : ℕ) [Fact p.Prime] {R : CommRingCat.{0}}
    (f g : Spec R ⟶ Spec (CommRingCat.of (Zloc p))) : f = g := by
  rw [← Spec.map_preimage f, ← Spec.map_preimage g]
  congr 1
  ext1
  exact IsLocalization.ringHom_ext (pIdeal p).primeCompl (RingHom.ext_int _ _)

/-- The ring map `ℤ_(p) → K` to a field of characteristic `0`. -/
def zlocTo (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharZero K] : Zloc p →+* K :=
  IsLocalization.lift (M := (pIdeal p).primeCompl) (g := Int.castRingHom K) (fun x => by
    have hx : (x : ℤ) ≠ 0 := fun h => x.2 (by rw [h]; exact Ideal.zero_mem _)
    exact isUnit_iff_ne_zero.2 (by simpa using hx))

/-- Fibres are invariant under isomorphism of objects. -/
theorem isFibreOf_of_iso {S : Scheme.{0}} (𝒜 : QMFamily S) {K : Type} [Field K]
    {y : Spec (CommRingCat.of K) ⟶ S} {P P' : QML3 K} (f : P.Iso P') (h : IsFibreOf 𝒜 y P') :
    IsFibreOf 𝒜 y P := by
  obtain ⟨k, hpb, hι, he⟩ := h
  have hiso : IsIso f.φ.hom.left := ⟨f.ψ.hom.left, by rw [← Over.comp_left, f.left]; rfl,
    by rw [← Over.comp_left, f.right]; rfl⟩
  have sq : IsPullback f.φ.hom.left P.A.X.hom P'.A.X.hom (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  refine ⟨f.φ.hom.left ≫ k, by simpa using sq.paste_horiz hpb, fun a => ?_, fun a => ?_⟩
  · have := congrArg CommaMorphism.left (f.equivariant a)
    simp only [Over.comp_left] at this
    simp only [Category.assoc]
    rw [reassoc_of% this, hι]
  · have hl := congrArg Additive.toMul (f.level a)
    simp only [toMul_ofMul] at hl
    rw [← he a, ← hl, Over.comp_left, Category.assoc]


/-! ## Hecke relabelings of a QM abelian scheme -/

/-- `ι ↦ ι ∘ α`, `η ↦ η ∘ α` on a `QMAbScheme`. -/
def twistAb {S : Scheme.{0}} (𝒜 : QMAbScheme S) (α : O ≃+* O) : QMAbScheme S where
  F := 𝒜.F
  proper := 𝒜.proper
  smooth := 𝒜.smooth
  iota a := 𝒜.iota (α a)
  iota_over a := 𝒜.iota_over (α a)
  eta a := 𝒜.eta (α a)
  eta_sec a := 𝒜.eta_sec (α a)
  grp := 𝒜.grp
  geomConn := 𝒜.geomConn
  one_eq := by rw [map_zero]; exact 𝒜.one_eq
  iota_hom a := 𝒜.iota_hom (α a)
  iota_one := by simp only [map_one]; exact 𝒜.iota_one
  iota_mul a b := by simp only [map_mul]; exact 𝒜.iota_mul _ _
  iota_add a b := by
    have h := 𝒜.iota_add (α a) (α b)
    rw [← map_add] at h
    exact h
  eta_add a b := by
    have h := 𝒜.eta_add (α a) (α b)
    rw [← map_add] at h
    exact h
  eta_linear a b := by simp only [map_mul]; exact 𝒜.eta_linear _ _
  eta_three b := by
    simp only [map_mul, map_ofNat, map_zero]
    exact 𝒜.eta_three _
  eta_ker K _ s a := by
    simp only [map_zero]
    rw [𝒜.eta_ker K s (α a)]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨α.symm c, by
        apply α.injective
        rw [hc, map_mul, RingEquiv.apply_symm_apply, map_ofNat]⟩
    · rintro ⟨c, rfl⟩
      exact ⟨α c, by rw [map_mul, map_ofNat]⟩

/-- `η ↦ η(· u)` on a `QMAbScheme`. -/
def rightMulAb {S : Scheme.{0}} (𝒜 : QMAbScheme S) (u : Oˣ) : QMAbScheme S where
  F := 𝒜.F
  proper := 𝒜.proper
  smooth := 𝒜.smooth
  iota := 𝒜.iota
  iota_over := 𝒜.iota_over
  eta a := 𝒜.eta (a * u)
  eta_sec a := 𝒜.eta_sec (a * u)
  grp := 𝒜.grp
  geomConn := 𝒜.geomConn
  one_eq := by rw [zero_mul]; exact 𝒜.one_eq
  iota_hom := 𝒜.iota_hom
  iota_one := 𝒜.iota_one
  iota_mul := 𝒜.iota_mul
  iota_add := 𝒜.iota_add
  eta_add a b := by
    have h := 𝒜.eta_add (a * u) (b * u)
    rw [← add_mul] at h
    exact h
  eta_linear a b := by rw [_root_.mul_assoc]; exact 𝒜.eta_linear _ _
  eta_three b := by rw [_root_.mul_assoc, zero_mul]; exact 𝒜.eta_three _
  eta_ker K _ s a := by
    rw [zero_mul, 𝒜.eta_ker K s (a * u)]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c * ↑u⁻¹, by
        rw [← _root_.mul_assoc, ← hc, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]⟩
    · rintro ⟨c, rfl⟩
      exact ⟨c * u, by rw [_root_.mul_assoc]⟩

/-- Identity pullback. -/
theorem qmFamFibre_id {S : Scheme.{0}} (𝒜 : QMFamily S) : QMFamFibre 𝒜 (𝟙 S) 𝒜 :=
  ⟨𝟙 _, IsPullback.of_horiz_isIso ⟨by simp⟩, fun a => by simp, fun a => by simp⟩

/-- Composition of relabeled pullbacks. -/
theorem qmFamFibre_comp {S : Scheme.{0}} (𝒜 : QMAbScheme S) (i j i' j' : O → O)
    (g g' : S ⟶ S) (h h' : 𝒜.F.left ⟶ 𝒜.F.left)
    (hpb : IsPullback h 𝒜.F.hom 𝒜.F.hom g) (hpb' : IsPullback h' 𝒜.F.hom 𝒜.F.hom g')
    (hi : ∀ a, 𝒜.iota (i a) ≫ h = h ≫ 𝒜.iota a) (he : ∀ a, 𝒜.eta (j a) ≫ h = g ≫ 𝒜.eta a)
    (hi' : ∀ a, 𝒜.iota (i' a) ≫ h' = h' ≫ 𝒜.iota a) (he' : ∀ a, 𝒜.eta (j' a) ≫ h' = g' ≫ 𝒜.eta a)
    (hii : ∀ a, i (i' a) = a) (hjj : ∀ a, j (j' a) = a) :
    QMFamFibre 𝒜.toQMFamily (g ≫ g') 𝒜.toQMFamily := by
  refine ⟨h ≫ h', hpb.paste_horiz hpb', fun a => ?_, fun a => ?_⟩
  · have := hi (i' a)
    rw [hii] at this
    rw [reassoc_of% this, hi', Category.assoc]
  · have := he (j' a)
    rw [hjj] at this
    rw [reassoc_of% this, he', Category.assoc]


instance zloc_noetherian (p : ℕ) [Fact p.Prime] : IsNoetherianRing (Zloc p) :=
  IsLocalization.isNoetherianRing (pIdeal p).primeCompl _ inferInstance

theorem isLocallyNoetherian_of_smooth (p : ℕ) [Fact p.Prime]
    (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))) (hsm : SmoothOfRelativeDimension 1 𝒴.hom) :
    IsLocallyNoetherian 𝒴.left := by
  have : Smooth 𝒴.hom := SmoothOfRelativeDimension.smooth 1 _
  exact LocallyOfFiniteType.isLocallyNoetherian 𝒴.hom

theorem paste_iota {X Y Z : Scheme.{0}} (e : X ⟶ X) (k : X ⟶ Y) (h : Y ⟶ Z) (ι : Y ⟶ Y)
    (ι' : Z ⟶ Z) (h1 : e ≫ k = k ≫ ι) (h2 : ι ≫ h = h ≫ ι') : e ≫ k ≫ h = (k ≫ h) ≫ ι' := by
  rw [reassoc_of% h1, h2, Category.assoc]

theorem paste_eta {X S Y Z W : Scheme.{0}} (e : X ⟶ Y) (k : Y ⟶ Z) (h : Z ⟶ W) (y : X ⟶ S)
    (η : S ⟶ Z) (g : S ⟶ S') (η' : S' ⟶ W) (h1 : e ≫ k = y ≫ η) (h2 : η ≫ h = g ≫ η') :
    e ≫ k ≫ h = (y ≫ g) ≫ η' := by
  rw [reassoc_of% h1, h2, Category.assoc]

/-! ## The reduction -/

/-- **`ShimuraGoodReductionNoGuard` from the printed representability and three pieces of glue**. -/
theorem shimuraGoodReductionNoGuard_of_rep (hRep : ShimuraIntegralModelRep)
    (g1 : QMAbFieldFibre) (g2 : QML3AsQMAb) (g3 : FibreClassUnique) :
    ShimuraGoodReductionNoGuard := by
  intro p _ hp
  obtain ⟨𝒴, 𝒜, hpr, hsm, hU⟩ := hRep p hp
  have hN := isLocallyNoetherian_of_smooth p 𝒴 hsm
  -- the Hecke automorphism attached to a relabeling with an inverse relabeling
  have hecke : ∀ (𝒜₁ 𝒜₂ : QMAbScheme 𝒴.left) (i j i' j' : O → O),
      𝒜₁.F = 𝒜.F → 𝒜₂.F = 𝒜.F → True := fun _ _ _ _ _ _ _ _ => trivial
  clear hecke
  refine ⟨𝒴, 𝒜.toQMFamily, hpr, hsm, fun K _ _ y => g1 _ 𝒜 K y, ?_, ?_, ?_, ?_⟩
  · -- injectivity on `ℚ̄`-points
    intro y y' P P' hP hP' hPP'
    obtain ⟨𝒜P, h𝒜P⟩ := g2 Qbar P
    obtain ⟨f⟩ := Quotient.exact hPP'
    have hP'' : IsFibreOf 𝒜.toQMFamily y' P := isFibreOf_of_iso _ f hP'
    have hyy : y' ≫ 𝒴.hom = y ≫ 𝒴.hom := spec_to_Zloc_ext p _ _
    obtain ⟨g, -, hg⟩ := hU (Over.mk (y ≫ 𝒴.hom)) (by dsimp; infer_instance) 𝒜P
    have e1 := hg (Over.homMk y rfl) ((h𝒜P _ _ y).mp hP)
    have e2 := hg (Over.homMk y' hyy) ((h𝒜P _ _ y').mp hP'')
    have := congrArg CommaMorphism.left (e1.trans e2.symm)
    simpa using this
  · -- surjectivity on `ℚ̄`-points
    intro P
    obtain ⟨𝒜P, h𝒜P⟩ := g2 Qbar P
    obtain ⟨g, hg, -⟩ := hU (Over.mk (Spec.map (CommRingCat.ofHom (zlocTo p Qbar))))
      (by dsimp; infer_instance) 𝒜P
    exact ⟨g.left, (h𝒜P _ _ g.left).mpr hg⟩
  · -- `Aut(𝒪)`
    intro α
    obtain ⟨g, ⟨h, hpb, hi, he⟩, -⟩ := hU 𝒴 hN (twistAb 𝒜 α)
    obtain ⟨g', ⟨h', hpb', hi', he'⟩, -⟩ := hU 𝒴 hN (twistAb 𝒜 α.symm)
    obtain ⟨g0, -, h0⟩ := hU 𝒴 hN 𝒜
    have hid : QMFamFibre 𝒜.toQMFamily (CommaMorphism.left (𝟙 𝒴)) 𝒜.toQMFamily :=
      qmFamFibre_id _
    have c1 : g ≫ g' = 𝟙 𝒴 := by
      refine (h0 _ ?_).trans (h0 _ hid).symm
      exact qmFamFibre_comp 𝒜 (fun a => α a) (fun a => α a) (fun a => α.symm a) (fun a => α.symm a)
        g.left g'.left h h' hpb hpb' hi he hi' he' (fun a => by simp) (fun a => by simp)
    have c2 : g' ≫ g = 𝟙 𝒴 := by
      refine (h0 _ ?_).trans (h0 _ hid).symm
      exact qmFamFibre_comp 𝒜 (fun a => α.symm a) (fun a => α.symm a) (fun a => α a) (fun a => α a)
        g'.left g.left h' h hpb' hpb hi' he' hi he (fun a => by simp) (fun a => by simp)
    refine ⟨⟨g, g', c1, c2⟩, fun y P P' hP hP' => ?_⟩
    rw [M3.twist_mk]
    refine g3 _ _ _ _ _ _ hP' ?_
    obtain ⟨k, hkpb, hki, hke⟩ := hP
    refine ⟨k ≫ h, hkpb.paste_horiz hpb, fun a => ?_, fun a => ?_⟩
    · exact paste_iota _ _ _ _ _ (hki (α a)) (hi a)
    · exact paste_eta _ _ _ _ _ _ _ (hke (α a)) (he a)
  · -- `𝒪^×`
    intro u
    obtain ⟨g, ⟨h, hpb, hi, he⟩, -⟩ := hU 𝒴 hN (rightMulAb 𝒜 u)
    obtain ⟨g', ⟨h', hpb', hi', he'⟩, -⟩ := hU 𝒴 hN (rightMulAb 𝒜 u⁻¹)
    obtain ⟨g0, -, h0⟩ := hU 𝒴 hN 𝒜
    have hid : QMFamFibre 𝒜.toQMFamily (CommaMorphism.left (𝟙 𝒴)) 𝒜.toQMFamily :=
      qmFamFibre_id _
    have c1 : g ≫ g' = 𝟙 𝒴 := by
      refine (h0 _ ?_).trans (h0 _ hid).symm
      exact qmFamFibre_comp 𝒜 (fun a : O => a) (fun a : O => a * (u : O)) (fun a : O => a)
        (fun a : O => a * ((u⁻¹ : Oˣ) : O)) g.left g'.left h h' hpb hpb' hi he hi' he' (fun a => rfl)
        (fun a => by rw [_root_.mul_assoc, Units.inv_mul, _root_.mul_one])
    have c2 : g' ≫ g = 𝟙 𝒴 := by
      refine (h0 _ ?_).trans (h0 _ hid).symm
      exact qmFamFibre_comp 𝒜 (fun a : O => a) (fun a : O => a * ((u⁻¹ : Oˣ) : O)) (fun a : O => a)
        (fun a : O => a * (u : O)) g'.left g.left h' h hpb' hpb hi' he' hi he (fun a => rfl)
        (fun a => by rw [_root_.mul_assoc, Units.mul_inv, _root_.mul_one])
    refine ⟨⟨g, g', c1, c2⟩, fun y P P' hP hP' => ?_⟩
    change M3.mk P' = M3.mk (P.rightMul u)
    refine g3 _ _ _ _ _ _ hP' ?_
    obtain ⟨k, hkpb, hki, hke⟩ := hP
    refine ⟨k ≫ h, hkpb.paste_horiz hpb, fun a => ?_, fun a => ?_⟩
    · exact paste_iota _ _ _ _ _ (hki a) (hi a)
    · exact paste_eta _ _ _ _ _ _ _ (hke (a * u)) (he a)

end HDec.SGRSplit
#print axioms HDec.SGRSplit.shimuraGoodReductionNoGuard_of_rep

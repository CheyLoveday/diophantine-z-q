import ZInQKernel.OneProof.H.TailZ14

/-! # c-to-printed, Part N: `ReductGlue.NeronLocalizesDVR` from BLR §1.2 Prop. 4 in its printed form

`NeronLocalizesDVR` (field `neronLocalizesDVR` of `OpenResearchLeaves10`) is proved here from
`BLR_1_2_4`, Bosch–Lütkebohmert–Raynaud's Prop. 1.2/4 stated over an arbitrary Dedekind domain and an
arbitrary smooth, separated `R`-scheme of finite type, with the Néron property of BLR §1.2 Def. 1 over
Mathlib's schemes (`IsNeronModelOver`). No group law, no abelian variety, no number field occur in the
leaf. -/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField

set_option linter.style.haveILetI false

namespace CToPrinted

/-- Verbatim copy of the field statement (`ZInQKernel/OneProof/H/TailZ14.lean`, `ReductGlue`). -/
def NeronLocalizesDVR : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒩 : ZInQ.DefFaltings.GroupModel A L), 𝒩.IsNeronModel →
    ∀ (O : ValuationSubring L) [IsDiscreteValuationRing O], (ReductGlue.toO 𝒩 O).IsNeronModel

example : NeronLocalizesDVR = ReductGlue.NeronLocalizesDVR := rfl

/-! ## The printed statement -/

/-- **Néron model** (BLR, *Néron models*, §1.2 Def. 1; UNVERIFIED locator). `R` a Dedekind domain with
field of fractions `K`, `X` an `R`-scheme. `X` is a Néron model of its generic fibre `X_K = X ×_R K` when
`X` is smooth, separated and of finite type over `R` and has the Néron mapping property: for every smooth
`R`-scheme `Y`, every `K`-morphism `Y_K → X_K` extends uniquely to an `R`-morphism `Y → X`, i.e.
`Hom_R(Y, X) → Hom_K(Y_K, X_K)`, `f ↦ f_K`, is bijective. (BLR define a Néron model of a given `X_K`;
"`X` is a Néron model of `X_K`" for an `R`-model `X` with generic fibre `X_K` is this predicate, the
identification `X ×_R K ≅ X_K` being transported by composition.) -/
def IsNeronModelOver (R K : Type) [CommRing R] [Field K] [Algebra R K]
    (X : Over (Spec (CommRingCat.of R))) : Prop :=
  Smooth X.hom ∧ IsSeparated X.hom ∧ LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom ∧
    ∀ (Y : Over (Spec (CommRingCat.of R))) [Smooth Y.hom],
      Function.Bijective fun f : Y ⟶ X =>
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map f

/-- **LEAF `BLR_1_2_4`** (Bosch–Lütkebohmert–Raynaud, *Néron models*, Ergebnisse 21 (1990), §1.2
Prop. 4; number and wording recalled, UNVERIFIED, no network). *Printed* (as recalled): let `R` be a
Dedekind domain with field of fractions `K`, `X_K` a smooth and separated `K`-scheme of finite type, and
`X` a smooth, separated `R`-model of `X_K` of finite type. Then `X` is a Néron model of `X_K` if and only
if, for every closed point `s` of `Spec R`, `X ⊗_R 𝒪_{S,s}` is a Néron model of `X_K` over `𝒪_{S,s}`.

*Lean form*: `𝒪_{S,s} = R_𝔭` is any ring with `IsLocalization.AtPrime R_𝔭 𝔭` (Mathlib's characteristic
predicate; every such ring is uniquely isomorphic to `Localization.AtPrime 𝔭`), with a compatible map to
`K`; `X ⊗_R R_𝔭` is the pullback along `Spec R_𝔭 → Spec R`; its generic fibre is `X_K` because
`R → R_𝔭 → K` is `R → K`. `X_K` is not a separate datum: the model is `X`, with its own generic fibre.
(Reading risk, flagged by reduct-glue §5: the print may use the strict henselizations `𝒪^{sh}_{S,s}`, or
both; the strict-henselization form is not stated here.) -/
def BLR_1_2_4 : Prop :=
  ∀ (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (X : Over (Spec (CommRingCat.of R))) [Smooth X.hom] [IsSeparated X.hom] [QuasiCompact X.hom],
    IsNeronModelOver R K X ↔
      ∀ (𝔭 : Ideal R) [𝔭.IsMaximal] (R𝔭 : Type) [CommRing R𝔭] [Algebra R R𝔭]
        [IsLocalization.AtPrime R𝔭 𝔭] [Algebra R𝔭 K] [IsScalarTower R R𝔭 K],
        IsNeronModelOver R𝔭 K ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R R𝔭)))).obj X)

/-! ## Glue: a discrete valuation ring of a number field is the localization at its center -/

section Loc

variable {L : Type} [Field L] [NumberField L]

/-- The algebra structure `𝓞_L → O` (`ReductGlue.toOL`), as a local definition. -/
@[reducible] noncomputable def algOL (O : ValuationSubring L) : Algebra (𝓞 L) O :=
  (ReductGlue.toOL O).toAlgebra

theorem isScalarTower_OL (O : ValuationSubring L) :
    letI := algOL O
    IsScalarTower (𝓞 L) O L := by
  letI := algOL O
  exact IsScalarTower.of_algebraMap_eq (fun _ => rfl)

/-- **`O = (𝓞_L)_{𝔭_O}`** as a characteristic predicate (from reduct-glue's `mem_iff_exists`). -/
theorem isLocalization_center (O : ValuationSubring L) [IsDiscreteValuationRing O] :
    letI := algOL O
    IsLocalization.AtPrime O (ReductGlue.center O) := by
  letI := algOL O
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨s, hs⟩
    exact ReductGlue.isUnit_toOL O hs
  · intro x
    obtain ⟨a, s, hs, h⟩ := (ReductGlue.mem_iff_exists O (x : L)).mp x.2
    refine ⟨⟨a, ⟨s, hs⟩⟩, ?_⟩
    apply Subtype.ext
    exact h
  · intro a b h
    refine ⟨1, ?_⟩
    have h' : ((a : L)) = (b : L) := congrArg (fun z : O => (z : L)) h
    have : a = b := RingOfIntegers.ext h'
    rw [this]

end Loc

/-! ## The field from the leaf -/

section Field

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- Postcomposition with an isomorphism does not change bijectivity. -/
theorem bijective_comp_iso {C : Type*} [Category C] {Y X : C} {Z W W' : C} (F : (Y ⟶ X) → (Z ⟶ W))
    (e : W ≅ W') : Function.Bijective (fun f => F f ≫ e.hom) ↔ Function.Bijective F := by
  have : (fun f => F f ≫ e.hom) = (fun g : Z ⟶ W => g ≫ e.hom) ∘ F := rfl
  rw [this]
  have hb : Function.Bijective (fun g : Z ⟶ W => g ≫ e.hom) :=
    ⟨fun g₁ g₂ h => by simpa using congrArg (· ≫ e.inv) h,
      fun g => ⟨g ≫ e.inv, by simp⟩⟩
  exact ⟨fun h => (Function.Bijective.of_comp_iff' hb F).mp h, fun h => hb.comp h⟩

/-- The kernel's Néron property of a group model is the printed one of its underlying scheme. -/
theorem isNeronModelOver_of (𝒩 : ZInQ.DefFaltings.GroupModel A L) (h : 𝒩.IsNeronModel) :
    IsNeronModelOver (𝓞 L) L 𝒩.G := by
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, fun Y _ => ?_⟩
  have hb := h Y
  refine ⟨fun a b hab => hb.1 ?_, fun g => ?_⟩
  · simp only at hab ⊢
    rw [hab]
  · obtain ⟨f, hf⟩ := hb.2 (g ≫ 𝒩.gen.hom)
    refine ⟨f, ?_⟩
    simp only at hf ⊢
    exact (cancel_mono 𝒩.gen.hom).mp hf

/-- **The field `neronLocalizesDVR` from the printed BLR 1.2/4.** -/
theorem neronLocalizesDVR_of_printed (hB : BLR_1_2_4) : ReductGlue.NeronLocalizesDVR := by
  intro K _ A L _ _ _ 𝒩 h𝒩 O _
  haveI := ReductGlue.center_isMaximal O
  letI := algOL O
  haveI := isScalarTower_OL O
  haveI := isLocalization_center O
  have h1 := isNeronModelOver_of 𝒩 h𝒩
  have h2 := ((hB (𝓞 L) L 𝒩.G).mp h1) (ReductGlue.center O) O
  obtain ⟨_, _, _, _, h3⟩ := h2
  have h4 : ∀ (Y : Over (Spec (CommRingCat.of O))) [Smooth Y.hom],
      Function.Bijective fun f : Y ⟶ (ReductGlue.toO 𝒩 O).G => (Over.pullback (ReductSplit.jO O)).map f :=
    h3
  intro Y _
  have hb := h4 Y
  refine ⟨fun a b hab => hb.1 ?_, fun g => ?_⟩
  · simp only at hab ⊢
    exact (cancel_mono (ReductGlue.toO 𝒩 O).gen.hom).mp hab
  · obtain ⟨f, hf⟩ := hb.2 (g ≫ (ReductGlue.toO 𝒩 O).gen.inv)
    refine ⟨f, ?_⟩
    simp only at hf ⊢
    rw [hf]
    simp

end Field

end CToPrinted

#print axioms CToPrinted.neronLocalizesDVR_of_printed

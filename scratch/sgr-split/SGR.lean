import ZInQKernel.OneProof.H.TailW
import ZInQKernel.OneProof.H.TailZ16

/-! sgr-split: `HDec.CurveSplitGR.ShimuraGoodReductionNoGuard` from the printed representability of the
integral moduli problem of QM abelian surfaces with level 3 (on the kernel's `QMAbScheme`). -/

noncomputable section

namespace HDec.SGRSplit

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV LeafQM.AV.R1UnivRigid VertWitness CurveSplitGR

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
    rw [reassoc_of% this, hι]
  · have hl := congrArg Additive.toMul (f.level a)
    simp only [toMul_ofMul] at hl
    rw [← he a, ← hl, Over.comp_left, Category.assoc]

end HDec.SGRSplit

import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate18Leaf
import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate18E2
import ZInQKernel.Contrib.RC53Assist.NoetherianInjective.GenuineInjective

/-!
# The common-coordinate leaf with the Kummer classes of the actual Heegner points

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-common-coordinate` (tex 4142–4194: "the actual
norm identity is `z_R = e_q i(z_P)`, with its retained boundary") through the inner limit of Lemma
`ex:limits-inner-limit` (tex 4385–4451), with the Heegner points of tex 2914–2936.

`CommonCoordinateInputsGenuineK` (`CommonCoordinate18Leaf.lean`) carries the class provider `HC`
as a named field. Here the provider is PINNED to lane E2's presentation classes of the Kummer
classes of the actual anchored Heegner points of the chain conductors `d_j = d ∏_{j' < j} ps[j']`
(`e2Provider`, `CommonCoordinate18E2.lean`, from lane E2's `gx`, `ux_spec`, `heegnerActual` and
`gx_step_heegner_at`):

* `e2ProviderOn`: the provider at the retained stages (all positive) from the inputs
  `E2ChainInputs` at each of them;
* **`CommonCoordinateInputsGenuineE2 D`**: `CommonCoordinateInputsGenuineK D` with `HC` the
  provider of lane E2's Kummer classes, one base conductor per address (the same `d` at every
  retained stage), and without the field `genuineInj`: the injectivity of the genuine local
  cochain modules is PROVED (`genuineCochainsInjective_proved`, Nöbeling with Bass–Papp), so the
  switch retractions rest on `MilneADT_I_2_8` and `IwasawaGenerators` only;
* **`commonCoordinateInputsGenuineK_of_E2`**, **`commonCoordinateInputsNF_of_genuineE2`**,
  **`commonCoordinateTarget_of_genuineE2`** (PROVED).

The step identities of the chain are then DERIVED from lane E2's global identities of the
Kummer classes of the actual points (`gx_step_heegner_at`, from the PRINT `CCLThm2_15Applied`
with the full anchor) through `exists_stepHyps_provider`; the classes are no longer free. The
remaining inputs of the classes are the fields of `E2ChainInputs`: the PRINT (Cai–Chen–Liu with the
full anchor), the ELLIOT `ThetaOfDelta f` (tex 2847–2855), and definitions (the conductor, its
admissibility, the supports, the splitting of the step primes, `hψ`).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open NumberField IsDedekindDomain
open Matrix Filter ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Central
  ZInQ.Manuscript.RC.Uniform ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CommonCoordinate
open ZInQ.Manuscript.RC.Limits (stageIdeal SplitInclusion MilneADT_I_2_8)
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.Local (IwasawaGenerators genuineCochainsInjective_proved)
open scoped PowerSeries.WithPiTopology

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

variable {ℓ : ℕ} [(Ecurve ℓ).IsElliptic] {C : TateCoef (Ecurve ℓ)} {D : RCData ℓ}
  {Fam : Family} {x : Addr Fam.b}

/-- **The provider of lane E2's Kummer classes at the retained stages** (tex 4157–4172,
4385–4451): at a stage `t + 1` of `G` the provider `e2Provider` of the inputs at that stage; at
the stage `0` (never retained) the zero provider. Kind: definition. -/
noncomputable def e2ProviderOn (A : ActualPresentation C D Fam x) {G : Set ℕ}
    (I : ∀ t, t + 1 ∈ G → E2ChainInputs A t) : ∀ s, s ∈ G → StageClassesAt A s
  | 0, _ => StageClassesAt.zero A 0
  | t + 1, h => e2Provider A t (I t h)

/-- The provider at a positive stage is lane E2's (tex 4157–4172). Kind: PROVED. -/
theorem e2ProviderOn_succ (A : ActualPresentation C D Fam x) {G : Set ℕ}
    (I : ∀ t, t + 1 ∈ G → E2ChainInputs A t) (t : ℕ) (h : t + 1 ∈ G) :
    e2ProviderOn A I (t + 1) h = e2Provider A t (I t h) :=
  rfl

/-- **The common-coordinate inputs with the Kummer classes of the actual Heegner points**
(tex 2914–2936, 4142–4194, 4385–4451): `CommonCoordinateInputsGenuineK` with the class provider
pinned to lane E2's (`e2ProviderOn`), one base conductor per address, and the injectivity of the
genuine local cochain modules discharged by `genuineCochainsInjective_proved`.
Kind: definition. -/
structure CommonCoordinateInputsGenuineE2 {ℓ : ℕ} (D : RCData ℓ) : Prop where
  /-- `E_ℓ` is elliptic (definition) -/
  elliptic : (Ecurve ℓ).IsElliptic
  /-- PRINT (paraphrased): Milne, *Arithmetic Duality Theorems*, I.2.8; the comparison with the
  cochain model is GLUE (tex 3470–3487) -/
  milne : MilneADT_I_2_8
  /-- GLUE: Iwasawa 1955, the tame quotient, joined with the splitting over the wild inertia
  (tex 3470–3480) -/
  iwasawa : IwasawaGenerators
  /-- one ultrafilter and one moving character per final family; at every address an actual
  presentation with the family's moving character and the Kummer places above `2N`, the inputs
  of lane E2's Kummer classes of the actual Heegner points at every retained stage with one base
  conductor (PRINT, ELLIOT, definitions: `E2ChainInputs`), and the genuine stage chains with
  these classes (data, ELLIOT, GLUE; tex 2720–2760, 2914–2936, 3455–3498, 4142–4194,
  4385–4451) -/
  chains : ∃ C : TateCoef (Ecurve ℓ), ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F →
    ∃ (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ cofinite) (Φ : FamilyCharacter C.K),
      ∀ x : Addr F.b, ∃ A : ActualPresentation C D F x,
        A.FromFamily Φ ∧ A.Pk = placesAboveTwoN C.K ℓ ∧
        ∃ (_ : DecidableEq (Places C.K A.S₀)) (G : Set ℕ)
          (I : ∀ t, t + 1 ∈ G → E2ChainInputs A t),
          (∀ t (h : t + 1 ∈ G) t' (h' : t' + 1 ∈ G), (I t h).d = (I t' h').d) ∧
          Nonempty (GenuineStageSTUK A milne iwasawa genuineCochainsInjective_proved U hU G
            (e2ProviderOn A I))

/-- **The leaf with a named provider from the leaf with lane E2's Kummer classes**
(tex 4142–4194, 4385–4451). Kind: PROVED. -/
theorem commonCoordinateInputsGenuineK_of_E2 {ℓ : ℕ} {D : RCData ℓ}
    (h : CommonCoordinateInputsGenuineE2 D) : CommonCoordinateInputsGenuineK D := by
  obtain ⟨hE, h28, hI, C, hC⟩ := h
  refine ⟨hE, h28, hI, genuineCochainsInjective_proved, C, fun Co Ce F hF => ?_⟩
  obtain ⟨U, hU, Φ, hx⟩ := hC Co Ce F hF
  refine ⟨U, hU, Φ, fun x => ?_⟩
  obtain ⟨A, hΦ, hPk, hdec, G, I, -, hGs⟩ := hx x
  exact ⟨A, hΦ, hPk, hdec, G, e2ProviderOn A I, hGs⟩

/-- **The current leaf from the leaf with lane E2's Kummer classes** (tex 4142–4194, 4385–4451):
the replacement of `CommonCoordinateInputsNF` in the leaves. Kind: PROVED. -/
theorem commonCoordinateInputsNF_of_genuineE2 {ℓ : ℕ} {D : RCData ℓ}
    (h : CommonCoordinateInputsGenuineE2 D) : CommonCoordinateInputsNF D :=
  commonCoordinateInputsNF_of_genuineK (commonCoordinateInputsGenuineK_of_E2 h)

/-- **(4.7) from the leaf with lane E2's Kummer classes** (tex 4142–4194, 4385–4451):
`RCSteps.common_coordinate`. Kind: PROVED. -/
theorem commonCoordinateTarget_of_genuineE2 {ℓ : ℕ} {D : RCData ℓ}
    (h : CommonCoordinateInputsGenuineE2 D) : CommonCoordinateTarget D :=
  commonCoordinateTarget_of_NF (commonCoordinateInputsNF_of_genuineE2 h)

end ZInQ.Manuscript.RC.Wiring

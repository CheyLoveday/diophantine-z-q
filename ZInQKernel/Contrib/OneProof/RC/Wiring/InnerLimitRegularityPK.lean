import ZInQKernel.Contrib.OneProof.RC.Wiring.InnerLimitRegularity
import ZInQKernel.Contrib.OneProof.RC.Wiring.GenuineSwitchPKNonVacuity

/-!
**Theorem 5.3, Lane RC0 round 11: the inner-limit regularity leaf on the primitive kernel vector**

Proposition `ex:limits-uniform-lower-bound`, height-one regularity (tex 4976–5200), on the
inner-limit route of `ILSwitchInputs` (the switches at derivative labels taken in the inner limit,
tex 5027–5086; Lemma `ex:limits-derivative-switch`, tex 4834–4907; Lemma `ex:limits-inner-limit`,
tex 4385–4451).

**The departure removed.** `ILSwitchInputs` copies the RC53 group's `InnerLimitSwitchInputs`,
whose field `primitive` (`∃ i, ρ ((stage c).z i) ≠ 0` at every reached configuration) asks the
actual class itself to be primitive. The text asks only that the actual class be nonzero, and
derives a primitive kernel vector from it (tex 4987–4992): "Choose a primitive vector `v ∈ ker d`.
Such a vector exists because `ker d` is saturated in `R^s` [...] The actual class `z` is a nonzero
fraction-field multiple of `v`." At the later configurations the new class spans the new generic
kernel and "we do not replace the actual class by the chosen primitive vector" (tex 5137–5147);
"each new generic kernel has rank one and has a primitive integral vector, so its fiber dimension
is at least one" (tex 5154–5157). On the inner-limit route `primitive` is consumed only for that
last statement: `InnerLimitSwitchInputs.toGalois` passes it to `GaloisSwitchData.primitive`,
`GaloisSwitchData.toHeightOneSwitchData` to `HeightOneSwitchData.primitive`, and
`HeightOneSwitchData.toProcess` reads it only in `pos` (fiber dimension at least one, through
`TwoTermStage.one_le_fiberDim`). No step, no coordinate step and no terminal argument uses it.

**The new structure.** `ILSwitchInputsPK P Cn W hW Φ ι u` has the fields of `ILSwitchInputs`, with
`primitive` replaced by `class_ne_zero`: the actual class of every reached configuration is
NONZERO in `Λ_𝔭` (`∃ i, (stage c).z i ≠ 0`), not modulo `𝔭`. The primitive kernel vector is not an
input: over the DVR `Λ_𝔭` it is PROVED by the text's saturation argument (the RC53 group's
`exists_primitiveKernelVector`), and `pos` follows from it inside the RC53 group's
`HeightOneSwitchDataPK.toProcess` (`one_le_fiberDim_of_primitiveKernel`).

PROVED here:
* `ILSwitchInputsPK.primitiveKernel`: over the DVR `Λ_𝔭`, every reached configuration has a
  primitive kernel vector of which its actual class is a nonzero fraction-field multiple;
* `ILSwitchInputsPK.toSwitchDataPK`: the RC53 group's `HeightOneSwitchDataPK`, built directly from
  the stages, the models and the steps: the reached configurations, the primitive kernel vectors,
  and at each switch the nonquadratic dimensions of the inner-limit step
  (`ILStageStep.toStepData`, `InnerLimitStepData.toStep`, `QuasiNonquadStep.toNonquadDims`, as
  `GaloisSwitchData.toHeightOneSwitchData` does on `InnerLimitSwitchInputs.toGalois`); the quadratic
  fields are vacuous (`hnq`);
* `regular_of_ILSwitchInputsPK` (`Λ_𝔭` a DVR) and `regular_of_ILSwitchInputsPK_of_height_one`
  (`𝔭` of height one): `∃ a, ι a = u`, through `regular_of_switchDataPK`;
* cross-check `ILSwitchInputsPK.toSwitchDataS`, `regular_of_ILSwitchInputsPK_noDVR`: the same
  conclusion with no DVR, through lane RC0's `HeightOneSwitchDataS` (`pos` from the nonzero class
  by semicontinuity); the DVR is needed only for the primitive kernel vector itself;
* `ILSwitchInputs.toPK`: a primitive class is nonzero, so the old inputs give the new ones with the
  same stages, models and steps;
* the leaves `RegularityInputsILPK`, `PrimRegularityInputsILPK` (as `RegularityInputsIL`,
  `PrimRegularityInputsIL`, with `ILSwitchInputsPK`; the quadratic branch stays
  `GenuineSwitchDataPK`), their consumers `RegularityInputsILPK.mem_lambdaHalf`,
  `RegularityInputsILPK.toS`, `primLambdaHalf_of_inputsILPK`, `heightOneTarget_of_inputsILPK`,
  `primRegularityInputsS_of_ILPK`, `primRegularityInputs_of_ILPK`, and the conversions from the
  old leaves `RegularityInputsIL.toPK`, `PrimRegularityInputsIL.toPK`;
* ties: `ILSwitchInputsPK.fiberDim_eq`, `ILSwitchInputsPK.one_le_h1`,
  `isEmpty_ILSwitchInputsPK_of_h1_eq_zero`, and the contrast
  `isEmpty_ILSwitchInputs_of_zAct_eq_zero` (the old inputs pin the actual fiber class to be
  nonzero; the new ones do not).

**The weakening is strict** (last section; the only use of the round 8 non-vacuity import):
`zeroClassILData` (new inputs over round 8's `zeroClassFamily F`, actual class `a ∈ 𝔪`, `a ≠ 0`,
from a model of `F` by the one-stage fibre; no switch, so no inner-limit step is needed),
`zeroClassILData_not_primitive`, `zeroClassFamily_no_IL` (no old inputs for any coordinate), and
`ilLeafContrast_of_unitFibre`: under round 8's hypothesis `E` at one height-one prime `𝔭` with a
nonquadratic specialization, a family genuine at `𝔭` with new inputs at a nonzero coordinate (actual
class the uniformizer of `Λ_𝔭`) over which no old inputs exist, for every actual conjugation and
curve. As for round 8's `leafContrast_of_unitFibre`, `E` (a genuine Galois Selmer complex over
`k(𝔭)` homotopy equivalent to `[k --0--> k]`) is not formalized. Also
`primRegularityInputsILPK_of_uPrim_zero` (the leaf is satisfiable through its `u = 0` branch).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open CategoryTheory Filter NumberField IsDedekindDomain IsLocalRing Module
open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.UniformSwitch
open ZInQ.Contrib.CloudB3RC53.SwitchInputs (SwitchFamily Reach InnerLimitStepData
  QuasiNonquadStep fiberH1 twoTermFiberComplex fiberDim_eq_h1)
open ZInQ.Manuscript.RC.Rings (isDiscreteValuationRing_atPrime_of_height_one)
open ZInQ.Manuscript.RC.Uniform (Lambda lambdaHalfToFrac mem_range_lambdaHalf_iff_forall_height_one)
open ZInQ.Manuscript.RC.CoefModules (ActualConj)
open ZInQ.Manuscript.RC.LambdaCoef (HasFullTwoTorsion)

/-! **The inner-limit inputs on the primitive kernel vector** -/

section Family

variable (P : Ideal Lambda) [P.IsPrime] {F : Type} [Field F]
variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (Cn : ActualConj K S) (W : WeierstrassCurve K) (hW : W.map (Cn.κ : K →+* K) = W)
  [W.IsElliptic] [HasFullTwoTorsion K S W]

/-- **Nonquadratic switching inputs on the inner-limit route, on the text's primitive kernel
vector** (tex 4976–5195): the fields of `ILSwitchInputs` (stage models of the family's fibres, the
starting link, nonquadraticity, the inner-limit steps `ILStageStep` whose sides are the family's
fibres; tex and kinds as there), except that the actual class of every reached configuration is
only asked to be NONZERO in `Λ_𝔭` (`class_ne_zero`; tex 4992, 5137–5144; ELLIOT), not primitive.
The primitive kernel vector of tex 4987–4991 is PROVED from it over the DVR `Λ_𝔭`
(`ILSwitchInputsPK.primitiveKernel`). Kind: definition (inputs). -/
structure ILSwitchInputsPK (Φ : SwitchFamily (ResAt P) (Localization.AtPrime P))
    (ι : Localization.AtPrime P →+* F) (u : F) where
  /-- The stage two-term models. -/
  stage : Φ.Config → TwoTermStage ι
  /-- Each stage models the family's fibre. -/
  model : ∀ c, HomotopyEquiv (selCx (Φ.fibre c)).toCC (twoTermFiberComplex (resAt P) (stage c))
  /-- The actual class. -/
  hz0 : ((model Φ.actual).hom.f 1).hom Φ.zAct = fun i => resAt P ((stage Φ.actual).z i)
  /-- The actual paired functional. -/
  hw0 : ∀ y, Φ.lamAct y = (fun i => resAt P ((stage Φ.actual).w i)) ⬝ᵥ
    (((model Φ.actual).hom.f 2).hom y : Fin _ → ResAt P)
  /-- The actual coordinate. -/
  hu0 : (stage Φ.actual).u = u
  /-- The specialization is nonquadratic. -/
  hnq : ¬ Φ.quadratic (resAt P)
  /-- tex 4992, 5137–5144: the actual class of every reached configuration is nonzero ("a nonzero
  fraction-field multiple of `v`"; the new class spans the new generic kernel). -/
  class_ne_zero : ∀ c, Reach Φ.next Φ.actual c → ∃ i, (stage c).z i ≠ 0
  /-- The inner-limit switch steps, with sides the family's fibres. -/
  step : ∀ c, Reach Φ.next Φ.actual c → 1 < (stage c).fiberDim (resAt P) →
    ∃ p : Φ.Prime, Nonempty (CoordStep ι (stage c).u (stage (Φ.next c p)).u) ∧
      ∃ X : ILStageStep P Cn W hW (stage c) (stage (Φ.next c p)),
        X.toStepData.toStep.SF.Dside = Φ.fibre c ∧
          X.toStepData.toStep.SS.Dside = Φ.fibre (Φ.next c p)

variable {P Cn W hW}

/-- **The old inputs give the new**: `ILSwitchInputs` gives `ILSwitchInputsPK` with the same
stages, models and steps (a primitive class is nonzero: if `z i = 0` then `ρ (z i) = 0`).
Kind: PROVED. -/
def ILSwitchInputs.toPK {Φ : SwitchFamily (ResAt P) (Localization.AtPrime P)}
    {ι : Localization.AtPrime P →+* F} {u : F} (X : ILSwitchInputs P Cn W hW Φ ι u) :
    ILSwitchInputsPK P Cn W hW Φ ι u where
  stage := X.stage
  model := X.model
  hz0 := X.hz0
  hw0 := X.hw0
  hu0 := X.hu0
  hnq := X.hnq
  class_ne_zero c hc := by
    obtain ⟨i, hi⟩ := X.primitive c hc
    exact ⟨i, fun h => hi (by rw [h, map_zero])⟩
  step := X.step

namespace ILSwitchInputsPK

variable {Φ : SwitchFamily (ResAt P) (Localization.AtPrime P)}
  {ι : Localization.AtPrime P →+* F} {u : F}

/-- **The fiber dimensions are the genuine ones**: every stage's fiber dimension is `dim_k H¹` of
its configuration's fibre (the RC53 group's `fiberDim_eq_h1` at the model). Kind: PROVED. -/
theorem fiberDim_eq (X : ILSwitchInputsPK P Cn W hW Φ ι u) (c : Φ.Config) :
    (X.stage c).fiberDim (resAt P) = finrank (ResAt P) ((selCx (Φ.fibre c)).toCC.homology 1) :=
  fiberDim_eq_h1 (ResAt P) (Localization.AtPrime P) F ι (resAt P) (X.stage c) (Φ.fibre c)
    ⟨X.model c⟩

/-- **The actual fibre has nonzero `H¹`** (the actual class is nonzero, so the fiber dimension is
at least one by lane RC0's `TwoTermStage.one_le_fiberDim_of_ne_zero`; no DVR needed). Over a DVR
this is also `one_le_fiberDim_of_primitiveKernel` at `primitiveKernel`. Kind: PROVED. -/
theorem one_le_h1 (hι : Function.Injective ι) (X : ILSwitchInputsPK P Cn W hW Φ ι u) :
    1 ≤ finrank (ResAt P) ((selCx (Φ.fibre Φ.actual)).toCC.homology 1) := by
  rw [← X.fiberDim_eq]
  obtain ⟨i, hi⟩ := X.class_ne_zero Φ.actual Reach.start
  exact TwoTermStage.one_le_fiberDim_of_ne_zero hι (resAt P) _ fun h => hi (congrFun h i)

/-- **The primitive kernel vector of every reached configuration** (tex 4987–4992; tex 5131–5134,
5154–5157 at the later configurations): over the DVR `Λ_𝔭`, with `ι` injective, the actual class of
a reached configuration, nonzero by `class_ne_zero`, is a nonzero fraction-field multiple of a
primitive vector `v ∈ ker d` with `v̄ ≠ 0` (the RC53 group's `exists_primitiveKernelVector`, the
saturation of `ker d`). Kind: PROVED. -/
theorem primitiveKernel [IsDiscreteValuationRing (Localization.AtPrime P)]
    (hι : Function.Injective ι) (X : ILSwitchInputsPK P Cn W hW Φ ι u) (c : Φ.Config)
    (hc : Reach Φ.next Φ.actual c) : Nonempty (PrimitiveKernelVector (X.stage c) (resAt P)) :=
  exists_primitiveKernelVector hι (resAt P) (X.stage c) (X.class_ne_zero c hc)

/-- **The text-faithful switching data of the inner-limit inputs** (tex 4976–5195): the RC53
group's `HeightOneSwitchDataPK`, built directly from the stages, models and steps. Stages: the
reached configurations; primitive kernel vectors: `primitiveKernel`; at a reached configuration
with fiber dimension `> 1`, the switch to `next c p` with its coordinate step and the nonquadratic
dimensions `NonquadDims s s'` of the inner-limit step (`ILStageStep.toStepData`,
`InnerLimitStepData.toStep`, `QuasiNonquadStep.toNonquadDims`; the dimension count (5.5a) and
`U = F` from the inner-limit duality, tex 4997–5003, 5055–5086). The sign dimensions are the
trivial ones `s₊ = s`, `s₋ = 0`; they are read only at a quadratic specialization, which `hnq`
excludes, so the quadratic switch fields are vacuous. Kind: PROVED. -/
def toSwitchDataPK [IsDiscreteValuationRing (Localization.AtPrime P)]
    (hι : Function.Injective ι) (X : ILSwitchInputsPK P Cn W hW Φ ι u) :
    HeightOneSwitchDataPK ι (resAt P) where
  Stage := {c // Reach Φ.next Φ.actual c}
  stage s := X.stage s.1
  quadratic := Φ.quadratic (resAt P)
  sp s := (X.stage s.1).fiberDim (resAt P)
  sm _ := 0
  sign_sum _ _ := add_zero _
  primitiveKernel s := X.primitiveKernel hι s.1 s.2
  switch_mixed s _ h1 := by
    obtain ⟨p, hcs, Y, -, -⟩ := X.step s.1 s.2 h1
    exact ⟨⟨Φ.next s.1 p, Reach.step p s.2⟩, hcs, fun q => absurd q X.hnq,
      fun _ => ⟨Y.toStepData.toStep.toNonquadDims⟩⟩
  switch_single _ q := absurd q X.hnq

/-- **Cross-check: the refined switching data of the inputs, with no DVR** (lane RC0's
`HeightOneSwitchDataS`, whose `pos` comes from the nonzero actual class itself, by
`TwoTermStage.one_le_fiberDim_of_ne_zero`): the reached configurations, the trivial sign
involution (read only at a quadratic specialization, which `hnq` excludes), and at each switch the
nonquadratic inputs `NonquadInputs` of the inner-limit step (its duality `U = U^⊥`, its detection
`F ≤ U` and the two (5.5a) equations of `QuasiNonquadStep.toNonquadDims`). Kind: PROVED. -/
def toSwitchDataS (X : ILSwitchInputsPK P Cn W hW Φ ι u) : HeightOneSwitchDataS ι (resAt P) where
  Stage := {c // Reach Φ.next Φ.actual c}
  stage s := X.stage s.1
  quadratic := Φ.quadratic (resAt P)
  sign _ := LinearMap.id
  sign_invol _ _ := LinearMap.id_comp _
  class_ne_zero s h := by
    obtain ⟨i, hi⟩ := X.class_ne_zero s.1 s.2
    exact hi (congrFun h i)
  switch_mixed s _ h1 := by
    obtain ⟨p, hcs, Y, -, -⟩ := X.step s.1 s.2 h1
    refine ⟨⟨Φ.next s.1 p, Reach.step p s.2⟩, hcs, fun q => absurd q X.hnq, fun _ => ?_⟩
    exact ⟨Y.toStepData.toStep.ε, Y.toStepData.toStep.σ, Y.toStepData.toStep.J,
      Y.toStepData.toStep.hε, Y.toStepData.toStep.hσ, Y.toStepData.toStep.hJ2,
      Y.toStepData.toStep.R.U, _, Y.toStepData.toStep.hdual, Y.toStepData.toStep.hdet,
      Y.toStepData.toStep.toNonquadDims.hs, Y.toStepData.toStep.toNonquadDims.hs'⟩
  switch_single _ q := absurd q X.hnq

end ILSwitchInputsPK

/-- **Regularity from the inner-limit inputs on the primitive kernel vector** (tex 4976–5195):
when `Λ_𝔭` is a DVR and `ι` is injective, `∃ a, ι a = u`, through
`ILSwitchInputsPK.toSwitchDataPK` and the RC53 group's `regular_of_switchDataPK` at the actual
configuration. Kind: PROVED (from the inputs). -/
theorem regular_of_ILSwitchInputsPK [IsDiscreteValuationRing (Localization.AtPrime P)]
    {Φ : SwitchFamily (ResAt P) (Localization.AtPrime P)} {ι : Localization.AtPrime P →+* F}
    {u : F} (hι : Function.Injective ι) (X : ILSwitchInputsPK P Cn W hW Φ ι u) :
    ∃ a, ι a = u := by
  obtain ⟨a, ha⟩ := regular_of_switchDataPK hι
    (fun _ hx => (IsLocalRing.residue_eq_zero_iff _).2 hx) (X.toSwitchDataPK hι)
    ⟨Φ.actual, Reach.start⟩
  exact ⟨a, ha.trans X.hu0⟩

/-- **Regularity at a height-one prime**: `Λ_𝔭` is a DVR (lane RC20's
`isDiscreteValuationRing_atPrime_of_height_one`), so `regular_of_ILSwitchInputsPK` applies.
Kind: PROVED (from the inputs). -/
theorem regular_of_ILSwitchInputsPK_of_height_one (hP : P.height = 1)
    {Φ : SwitchFamily (ResAt P) (Localization.AtPrime P)} {ι : Localization.AtPrime P →+* F}
    {u : F} (hι : Function.Injective ι) (X : ILSwitchInputsPK P Cn W hW Φ ι u) :
    ∃ a, ι a = u := by
  have := isDiscreteValuationRing_atPrime_of_height_one P hP
  exact regular_of_ILSwitchInputsPK hι X

/-- **Cross-check: the same regularity with no DVR**: for any prime `𝔭` and injective `ι`,
`∃ a, ι a = u`, through `ILSwitchInputsPK.toSwitchDataS` and RC16's `regular_of_switchProcess`.
So the DVR is used only to produce the text's primitive kernel vector
(`ILSwitchInputsPK.primitiveKernel`), not for the regularity conclusion. Kind: PROVED (from the
inputs). -/
theorem regular_of_ILSwitchInputsPK_noDVR
    {Φ : SwitchFamily (ResAt P) (Localization.AtPrime P)} {ι : Localization.AtPrime P →+* F}
    {u : F} (hι : Function.Injective ι) (X : ILSwitchInputsPK P Cn W hW Φ ι u) :
    ∃ a, ι a = u := by
  obtain ⟨a, ha⟩ := ZInQ.Manuscript.RC.Uniform.regular_of_switchProcess
    (Reg := fun x : F => ∃ a, ι a = x)
    (fun x y ⟨a, ha⟩ ⟨b, hb⟩ => ⟨a * b, by rw [map_mul, ha, hb]⟩)
    (X.toSwitchDataS.toProcess hι (fun _ hx => (IsLocalRing.residue_eq_zero_iff _).2 hx)
      (fun x : F => ∃ a, ι a = x) (fun a => ⟨a, rfl⟩)) ⟨Φ.actual, Reach.start⟩
  exact ⟨a, ha.trans X.hu0⟩

/-- **No new inputs over a family whose actual fibre has `H¹ = 0`**, whatever the coordinate.
Kind: PROVED. -/
theorem isEmpty_ILSwitchInputsPK_of_h1_eq_zero
    {Φ : SwitchFamily (ResAt P) (Localization.AtPrime P)} {ι : Localization.AtPrime P →+* F}
    (hι : Function.Injective ι) (u : F)
    (h0 : finrank (ResAt P) ((selCx (Φ.fibre Φ.actual)).toCC.homology 1) = 0) :
    IsEmpty (ILSwitchInputsPK P Cn W hW Φ ι u) :=
  ⟨fun X => by have := X.one_le_h1 hι; omega⟩

/-- **The old inputs pin the actual fibre class**: over a family whose actual fibre class `zAct` is
`0` there are no `ILSwitchInputs`, whatever the coordinate (`hz0` makes the reduction of the
starting class the image of `zAct = 0`, which `primitive` forbids). The new inputs have no such
constraint: in the text the actual class `z = c · v` may be divisible by the uniformizer (tex
4987–4992), and then its reduction is `0`. Kind: PROVED. -/
theorem isEmpty_ILSwitchInputs_of_zAct_eq_zero
    {Φ : SwitchFamily (ResAt P) (Localization.AtPrime P)} {ι : Localization.AtPrime P →+* F}
    (h0 : Φ.zAct = 0) (u : F) : IsEmpty (ILSwitchInputs P Cn W hW Φ ι u) := by
  refine ⟨fun X => ?_⟩
  obtain ⟨i, hi⟩ := X.primitive Φ.actual Reach.start
  have h := X.hz0
  rw [h0, map_zero] at h
  have h' : (0 : Fin ((X.stage Φ.actual).n + 1) → ResAt P) =
      fun i => resAt P ((X.stage Φ.actual).z i) := h
  exact hi (by simpa using (congrFun h' i).symm)

end Family

/-! **The height-one leaf on the inner-limit route and the primitive kernel vector** -/

/-- **The height-one regularity inputs on the inner-limit route, on the text's primitive kernel
vector** (tex 4976–5200; replaces `RegularityInputsIL u`). Either `u = 0` (tex 5196–5197; ELLIOT),
or at every height-one prime `𝔭 ≠ (2)` of `Λ` a configuration family `Φ` over `Λ_𝔭`, genuine at `𝔭`
(`IsGenuineFamilyAt`; GLUE), with
* at a nonquadratic specialization: a field `K`, a set of places `S`, the actual conjugation and
  the curve over `K` fixed by it with full two-torsion (data; GLUE identification with the
  address's `K` and `E_K`), and `ILSwitchInputsPK` over `Φ` starting at `u` (the actual classes
  nonzero, not primitive; fields at `ILSwitchInputsPK`);
* at a quadratic specialization (`t̄ (t̄ + 2) = 0`, tex 5005–5008): `GenuineSwitchDataPK` over `Φ`
  (the single-sign switches; fields at `RegularityInputsGPK`).

Kind: definition. -/
def RegularityInputsILPK (u : FractionRing Lambda) : Prop :=
  u = 0 ∨ ∀ (P : Ideal Lambda) [P.IsPrime], P.height = 1 → P ≠ Ideal.span {2} →
    ∃ Φ : SwitchFamily (ResAt P) (Localization.AtPrime P), IsGenuineFamilyAt P Φ ∧
      ((∃ (K : Type) (_ : Field K) (_ : NumberField K) (S : Set (HeightOneSpectrum (𝓞 K)))
          (Cn : ActualConj K S) (W : WeierstrassCurve K) (hW : W.map (Cn.κ : K →+* K) = W)
          (_ : W.IsElliptic) (_ : HasFullTwoTorsion K S W),
          Nonempty (ILSwitchInputsPK P Cn W hW Φ (UniformSwitch.toFracAt P) u)) ∨
        (Φ.quadratic (resAt P) ∧
          Nonempty (GenuineSwitchDataPK Φ (UniformSwitch.toFracAt P) (resAt P) u)))

/-- **The old leaf gives the new one** (`ILSwitchInputs.toPK` in the nonquadratic branch; the
quadratic branch verbatim). Kind: PROVED. -/
theorem RegularityInputsIL.toPK {u : FractionRing Lambda} (h : RegularityInputsIL u) :
    RegularityInputsILPK u := by
  rcases h with h | h
  · exact Or.inl h
  · refine Or.inr fun P _ hP hne => ?_
    obtain ⟨Φ, hΦ, hb⟩ := h P hP hne
    refine ⟨Φ, hΦ, ?_⟩
    rcases hb with ⟨K, _, _, S, Cn, W, hW, _, _, ⟨X⟩⟩ | hq
    · exact Or.inl ⟨K, _, _, S, Cn, W, hW, _, _, ⟨X.toPK⟩⟩
    · exact Or.inr hq

/-- **`u ∈ Λ[1/2]` from the new inputs**: at every height-one prime `𝔭 ≠ (2)`, `Λ_𝔭` is a DVR (lane
RC20), so `u ∈ ι(Λ_𝔭)` by `regular_of_ILSwitchInputsPK` (nonquadratic) or
`regular_of_genuineSwitchDataPK` (quadratic); then the normal-domain intersection formula
(`mem_range_lambdaHalf_iff_forall_height_one`, tex 5190–5194). Kind: PROVED from the inputs. -/
theorem RegularityInputsILPK.mem_lambdaHalf {u : FractionRing Lambda}
    (h : RegularityInputsILPK u) : u ∈ lambdaHalfToFrac.range := by
  rw [mem_range_lambdaHalf_iff_forall_height_one]
  intro P _ hP hne
  rcases h with rfl | h
  · exact Subalgebra.zero_mem _
  · obtain ⟨Φ, -, hΦ⟩ := h P hP hne
    have := isDiscreteValuationRing_atPrime_of_height_one P hP
    rcases hΦ with ⟨K, _, _, S, Cn, W, hW, _, _, ⟨X⟩⟩ | ⟨-, ⟨G⟩⟩
    · obtain ⟨a, ha⟩ := regular_of_ILSwitchInputsPK (UniformSwitch.toFracAt_injective P) X
      rw [← ha]
      exact ⟨a, rfl⟩
    · obtain ⟨a, ha⟩ := regular_of_genuineSwitchDataPK (UniformSwitch.toFracAt_injective P)
        (fun _ hx => (IsLocalRing.residue_eq_zero_iff _).2 hx) G
      rw [← ha]
      exact ⟨a, rfl⟩

/-- `RegularityInputsILPK u → RegularityInputsS u` (through `u ∈ Λ[1/2]` and
`regularityInputsS_iff`). Kind: PROVED. -/
theorem RegularityInputsILPK.toS {u : FractionRing Lambda} (h : RegularityInputsILPK u) :
    RegularityInputsS u :=
  (regularityInputsS_iff u).mpr h.mem_lambdaHalf

section HeightOneTarget

variable {ℓ : ℕ} (D : RCData ℓ)

/-- **The height-one leaf on the inner-limit route and the text's primitive kernel vector**
(replaces `PrimRegularityInputsIL D`; tex 4976–5200, at the ring instances of the final field):
for every final family `F` and every address `x` there is `u ∈ Frac Λ` with
`IsTExpansion u (D.uPrim F x)` (tex 3877–3892; GLUE) and `RegularityInputsILPK u` (the actual
classes nonzero, not primitive; the primitive kernel vectors PROVED over the DVR `Λ_𝔭`).
Kind: definition. -/
def PrimRegularityInputsILPK : Prop :=
  ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b,
    ∃ u : FractionRing Lambda, IsTExpansion u (D.uPrim F x) ∧ RegularityInputsILPK u

/-- **The old leaf gives the new one** (`RegularityInputsIL.toPK` at every address).
Kind: PROVED. -/
theorem PrimRegularityInputsIL.toPK (h : PrimRegularityInputsIL D) : PrimRegularityInputsILPK D :=
  fun Co Ce F hF x =>
    let ⟨u, hT, hreg⟩ := h Co Ce F hF x
    ⟨u, hT, hreg.toPK⟩

/-- **`u_{prim,x} ∈ Λ[1/2]`** at every address of every final family, from the new leaf.
Kind: PROVED from the inputs. -/
theorem primLambdaHalf_of_inputsILPK (h : PrimRegularityInputsILPK D) :
    ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b,
      InLamHalf (D.uPrim F x) := by
  intro Co Ce F hF x
  obtain ⟨u, hT, hreg⟩ := h Co Ce F hF x
  exact inLamHalf_of_isTExpansion hT hreg.mem_lambdaHalf

/-- **`RCSteps.height_one`** (tex 4909–5205) from the new leaf and (4.7). Kind: PROVED from the
inputs. -/
theorem heightOneTarget_of_inputsILPK (h : PrimRegularityInputsILPK D)
    (h47 : CommonCoordinateTarget D) : HeightOneTarget D :=
  heightOneTarget_of_prim D (primLambdaHalf_of_inputsILPK D h) h47

/-- **Conversion to the round-3 leaf** `PrimRegularityInputsS D`. Kind: PROVED. -/
theorem primRegularityInputsS_of_ILPK (h : PrimRegularityInputsILPK D) :
    PrimRegularityInputsS D :=
  (primRegularityInputsS_iff D).mpr (primLambdaHalf_of_inputsILPK D h)

/-- **The old leaf `PrimRegularityInputs D`** (the form consumed by the base-zero step), from the
new leaf. Kind: PROVED. -/
theorem primRegularityInputs_of_ILPK (h : PrimRegularityInputsILPK D) : PrimRegularityInputs D :=
  primRegularityInputs_of_S D (primRegularityInputsS_of_ILPK D h)

end HeightOneTarget

/-! **The weakening is strict, and the leaf is satisfiable** -/

section Contrast

variable {P : Ideal Lambda} [P.IsPrime]
variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (Cn : ActualConj K S) (W : WeierstrassCurve K) (hW : W.map (Cn.κ : K →+* K) = W)
  [W.IsElliptic] [HasFullTwoTorsion K S W]

/-- **New inputs whose actual class `a ∈ 𝔪` is not primitive**, over round 8's
`zeroClassFamily F` (one configuration, fibre `F`, actual fibre class and functional `0`,
`t = X`), at a nonquadratic specialization, from a model `e` of `F` by the one-stage fibre: the
stage `[Λ_𝔭 --0--> Λ_𝔭]` with actual class and functional `a` and coordinate `a²` (round 8's
`scalarStageAt`). No switch is demanded (fiber dimension one), so no inner-limit step is needed;
the actual conjugation and the curve are arbitrary. Kind: definition. -/
def zeroClassILData (F : SelData (ResAt P)) (e : HomotopyEquiv (selCx F).toCC (unitFibre P))
    (hnq : ¬ resAt P (algebraMap Lambda (Localization.AtPrime P) PowerSeries.X) *
      (resAt P (algebraMap Lambda (Localization.AtPrime P) PowerSeries.X) + 2) = 0)
    (a : Localization.AtPrime P) (ha : a ∈ IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (ha0 : a ≠ 0) :
    ILSwitchInputsPK P Cn W hW (zeroClassFamily F) (UniformSwitch.toFracAt P)
      (UniformSwitch.toFracAt P (a ^ 2)) where
  stage _ := scalarStageAt P a
  model _ := e
  hz0 := by
    change (e.hom.f 1).hom (0 : (selCx F).toCC.X 1) = _
    rw [map_zero]
    show (0 : Fin (0 + 1) → ResAt P) = fun _ => resAt P a
    funext i
    exact ((IsLocalRing.residue_eq_zero_iff a).2 ha).symm
  hw0 y := by
    show (zeroClassFamily F).lamAct y =
      (fun _ => resAt P a) ⬝ᵥ ((e.hom.f 2).hom y : Fin (0 + 1) → ResAt P)
    have hra : resAt P a = 0 := (IsLocalRing.residue_eq_zero_iff a).2 ha
    simp only [dotProduct, hra, zero_mul, Finset.sum_const_zero]
    rfl
  hu0 := rfl
  hnq := hnq
  class_ne_zero _ _ := ⟨0, ha0⟩
  step _ _ h := absurd h (by rw [scalarStageAt_fiberDim]; exact lt_irrefl 1)

/-- **The actual class of the example is not primitive** (it reduces to `0`). Kind: PROVED. -/
theorem zeroClassILData_not_primitive (F : SelData (ResAt P))
    (e : HomotopyEquiv (selCx F).toCC (unitFibre P))
    (hnq : ¬ resAt P (algebraMap Lambda (Localization.AtPrime P) PowerSeries.X) *
      (resAt P (algebraMap Lambda (Localization.AtPrime P) PowerSeries.X) + 2) = 0)
    (a : Localization.AtPrime P) (ha : a ∈ IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (ha0 : a ≠ 0) :
    ¬ ∃ i, resAt P (((zeroClassILData Cn W hW F e hnq a ha ha0).stage
      (zeroClassFamily F).actual).z i) ≠ 0 := by
  rintro ⟨i, hi⟩
  exact hi ((IsLocalRing.residue_eq_zero_iff a).2 ha)

/-- **The old inputs reject the example family for every coordinate** (its actual fibre class is
`0`; `isEmpty_ILSwitchInputs_of_zAct_eq_zero`). Kind: PROVED. -/
theorem zeroClassFamily_no_IL (F : SelData (ResAt P)) (u : FractionRing Lambda) :
    IsEmpty (ILSwitchInputs P Cn W hW (zeroClassFamily F) (UniformSwitch.toFracAt P) u) :=
  isEmpty_ILSwitchInputs_of_zAct_eq_zero rfl u

/-- **The weakening at the level of the leaf, under `E` at one nonquadratic prime**: if at a
height-one prime `𝔭` with `t̄ (t̄ + 2) ≠ 0` some genuine Galois Selmer datum `F` over `k(𝔭)` is
homotopy equivalent to the one-stage fibre, then for every actual conjugation and curve there is a
family genuine at `𝔭` with new inputs at a nonzero coordinate (actual class the uniformizer of
`Λ_𝔭`, not primitive), over which no old inputs exist for any coordinate. Kind: PROVED. -/
theorem ilLeafContrast_of_unitFibre (hP : P.height = 1) (F : SelData (ResAt P))
    (hF : IsGaloisSelData F) (e : HomotopyEquiv (selCx F).toCC (unitFibre P))
    (hnq : ¬ resAt P (algebraMap Lambda (Localization.AtPrime P) PowerSeries.X) *
      (resAt P (algebraMap Lambda (Localization.AtPrime P) PowerSeries.X) + 2) = 0) :
    ∃ (Φ : SwitchFamily (ResAt P) (Localization.AtPrime P)) (u : FractionRing Lambda),
      IsGenuineFamilyAt P Φ ∧ u ≠ 0 ∧
      Nonempty (ILSwitchInputsPK P Cn W hW Φ (UniformSwitch.toFracAt P) u) ∧
      ∀ u', IsEmpty (ILSwitchInputs P Cn W hW Φ (UniformSwitch.toFracAt P) u') := by
  have := isDiscreteValuationRing_atPrime_of_height_one P hP
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime P)
  have hm : ϖ ∈ IsLocalRing.maximalIdeal (Localization.AtPrime P) :=
    (IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit
  refine ⟨zeroClassFamily F, UniformSwitch.toFracAt P (ϖ ^ 2), ⟨fun _ => hF, rfl⟩, ?_,
    ⟨zeroClassILData Cn W hW F e hnq ϖ hm hϖ.ne_zero⟩, zeroClassFamily_no_IL Cn W hW F⟩
  exact (map_ne_zero_iff _ (UniformSwitch.toFracAt_injective P)).mpr (pow_ne_zero 2 hϖ.ne_zero)

/-- **`PrimRegularityInputsILPK D` is satisfiable** (through its `u = 0` branch) whenever the
primitive coordinates vanish (a degenerate witness, as for the earlier leaves). Kind: PROVED. -/
theorem primRegularityInputsILPK_of_uPrim_zero {ℓ : ℕ} (D : RCData ℓ)
    (hD : ∀ F x, D.uPrim F x = 0) : PrimRegularityInputsILPK D :=
  fun _ _ F _ x => ⟨0, by rw [hD F x]; exact isTExpansion_zero, Or.inl rfl⟩

end Contrast

end ZInQ.Manuscript.RC.Wiring

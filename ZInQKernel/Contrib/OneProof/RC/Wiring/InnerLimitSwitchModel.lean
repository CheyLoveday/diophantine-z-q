import ZInQKernel.Contrib.RC53Assist.SwitchInterface.Interface
import ZInQKernel.Contrib.OneProof.RC.Wiring.InnerLimitRegularityBounds
import ZInQKernel.Contrib.OneProof.RC.Wiring.GenuineSwitchHPK

/-!
# Theorem 5.3, Lane RC0 round 14: the inner-limit switch with side models

Proposition `ex:limits-uniform-lower-bound`, height-one regularity (tex 4976–5195), with the switch
at a derivative label taken on the inner-limit objects (tex 5027–5086, 4834–4907, 4385–4451).

The earlier inner-limit interfaces required the finite and singular sides of every switch to be
EQUAL to the configurations' fibres as Selmer data. For the inner-limit sides this rules out a
second switch, since a singular side is never a finite side as Selmer data (the RC53 group's
`finite_singular_ne`), so those interfaces are uninhabitable above fibre dimension three
(`no_inputs_of_large_actual_fibre`). The interfaces below replace the equalities by homotopy
equivalences of the Selmer complexes (the side models), keep the starting identifications of the
family, and ask the actual class of every reached configuration only to be nonzero (tex 4992,
5137–5144); the primitive kernel vector is then proved over the DVR `Λ_𝔭` (tex 4987–4992). The
descent uses only the step's side-to-stage cohomology isomorphisms and does not use the side
models. The side models are homotopy equivalences over the residue field `k(𝔭)`; given the frame
they amount to homotopy equivalences with the stages' two-term fibre complexes, i.e. each side has
the cohomology `k^s` in degrees one and two and zero elsewhere. In degree one this is already given
by `φ`, `φ'` and the frame's models; the side models add the other degrees. They are not required
to be compatible with `φ`, `φ'`, the frame's models, or the step's localization, strict, relaxed
and duality maps, and the step data are not tied to the chosen derivative label.

* `SwitchModelFrame`: the family frame (stages, models of the fibres, the starting class,
  functional and coordinate, nonquadraticity, the classes nonzero);
  `NonquadSwitchFrame.toModelFrame`: the RC53 group's frame, whose classes are residue-primitive,
  gives it.
* `SwitchModelInputs` (any coefficient rings): the frame and homology-level switch steps
  (`QuasiNonquadStep`) with side models. PROVED: `fiberDim_eq`, `toSwitchDataPK`,
  `regular_of_switchModelInputs` (over a DVR), `toSwitchDataS`,
  `regular_of_switchModelInputs_noDVR`.
* `InnerLimitSwitchModel` (over `Λ_𝔭`): the frame and inner-limit step data (`InnerLimitStepData`)
  with side models. PROVED: `toModelInputs`, `regular_of_innerLimitSwitchModel`.
* `RetainedActualStageLink`, `ILStageStepLinked`: the inputs of one switch on the actual stage
  Selmer complexes (`ILStageStepActual`, stage-dependent supports), together with the
  identifications of the stage prime's condition (in the old support, full), of the comparison with
  the split model (a homotopy equivalence), and of the retained realization with the actual stage
  complexes (their differentials, localization and global trace pairing in the retained
  coordinates).
* `InnerLimitSwitchActual`: the frame and such linked actual steps with side models. PROVED:
  `toInner`, `regular_of_innerLimitSwitchActual`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open CategoryTheory Filter NumberField IsDedekindDomain IsLocalRing Matrix Module
open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.UniformSwitch ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Contrib.RC53Assist.SwitchInterface (NonquadSwitchFrame)
open ZInQ.Manuscript.RC.Rings (isDiscreteValuationRing_atPrime_of_height_one)
open ZInQ.Manuscript.RC.Uniform (Lambda)

/-! **The model-level interface** -/

section Model

variable {k : Type} [Field k] {A F : Type} [CommRing A] [Field F]

/-- **The family frame** (tex 4976–5003): stages over `A`, homotopy equivalences of the
configurations' fibres with the stages' two-term fibres, the starting class, functional and
coordinate, the nonquadratic specialization, and the actual class of every reached configuration
nonzero (tex 4992, 5137–5144). Kind: definition (inputs). -/
structure SwitchModelFrame (Φ : SwitchFamily k A) (ι : A →+* F) (ρ : A →+* k) (u : F) where
  /-- The two-term stages (tex 4983–4987). -/
  stage : Φ.Config → TwoTermStage ι
  /-- Each stage models its configuration's fibre (tex 4976–4996). -/
  model : ∀ c, HomotopyEquiv (selCx (Φ.fibre c)).toCC (twoTermFiberComplex ρ (stage c))
  /-- The actual class. -/
  hz0 : ((model Φ.actual).hom.f 1).hom Φ.zAct = fun i => ρ ((stage Φ.actual).z i)
  /-- The actual paired functional. -/
  hw0 : ∀ y, Φ.lamAct y =
    (fun i => ρ ((stage Φ.actual).w i)) ⬝ᵥ (((model Φ.actual).hom.f 2).hom y : Fin _ → k)
  /-- The actual coordinate (tex 4986–4992). -/
  hu0 : (stage Φ.actual).u = u
  /-- The specialization is nonquadratic (tex 5005–5008). -/
  hnq : ¬ Φ.quadratic ρ
  /-- The actual class of every reached configuration is nonzero (tex 4992, 5137–5144). -/
  class_ne_zero : ∀ c, Reach Φ.next Φ.actual c → ∃ i, (stage c).z i ≠ 0

variable {Φ : SwitchFamily k A} {ι : A →+* F} {ρ : A →+* k} {u : F}

/-- **The RC53 group's frame gives the frame**: a residue-primitive class is nonzero. Kind:
PROVED. -/
def NonquadSwitchFrame.toModelFrame (X : NonquadSwitchFrame Φ ι ρ u) :
    SwitchModelFrame Φ ι ρ u where
  stage := X.stage
  model := X.model
  hz0 := X.hz0
  hw0 := X.hw0
  hu0 := X.hu0
  hnq := X.hnq
  class_ne_zero c hc := by
    obtain ⟨i, hi⟩ := X.primitive c hc
    exact ⟨i, fun h => hi (by rw [h, map_zero])⟩

/-- **The fiber dimensions are those of the fibres**. Kind: PROVED. -/
theorem SwitchModelFrame.fiberDim_eq (X : SwitchModelFrame Φ ι ρ u) (c : Φ.Config) :
    (X.stage c).fiberDim ρ = finrank k ((selCx (Φ.fibre c)).toCC.homology 1) :=
  fiberDim_eq_h1 k A F ι ρ (X.stage c) (Φ.fibre c) ⟨X.model c⟩

/-- **Switching inputs with side models** (tex 4976–5195): the frame and, at each reached
configuration with fiber dimension `> 1`, a successor with a coordinate step and a homology-level
nonquadratic step (`QuasiNonquadStep`: the relaxed localization, the finite and singular sides,
the duality `U = U^⊥`, the detection `F ≤ U`, the side-to-stage cohomology isomorphisms), whose
side Selmer complexes are homotopy equivalent to the fibres of the configuration and of its
successor (over `k(𝔭)`; given the frame, equivalently to the stages' two-term fibre complexes:
isomorphic cohomology in every degree, with no compatibility with the step's maps; tex 4997–5003,
5040–5086). Kind: definition (inputs). -/
structure SwitchModelInputs (Φ : SwitchFamily k A) (ι : A →+* F) (ρ : A →+* k) (u : F)
    extends SwitchModelFrame Φ ι ρ u where
  /-- The switches, with side models. -/
  step : ∀ c, Reach Φ.next Φ.actual c → 1 < (stage c).fiberDim ρ →
    ∃ p : Φ.Prime, Nonempty (CoordStep ι (stage c).u (stage (Φ.next c p)).u) ∧
      ∃ N : QuasiNonquadStep ρ (stage c) (stage (Φ.next c p)),
        Nonempty (HomotopyEquiv (selCx N.SF.Dside).toCC (selCx (Φ.fibre c)).toCC) ∧
        Nonempty (HomotopyEquiv (selCx N.SS.Dside).toCC (selCx (Φ.fibre (Φ.next c p))).toCC)

namespace SwitchModelInputs

/-- **The text's switching data of the inputs** over a DVR (tex 4976–5195): the reached
configurations as stages, the primitive kernel vectors by saturation (the RC53 group's
`exists_primitiveKernelVector`, tex 4987–4992), and at each switch the nonquadratic dimension
inputs of its step (`QuasiNonquadStep.toNonquadDims`, tex 4997–5003); the sign dimensions are the
trivial ones, read only at a quadratic specialization, which `hnq` excludes. Kind: PROVED. -/
def toSwitchDataPK [IsDomain A] [IsDiscreteValuationRing A] (hι : Function.Injective ι)
    (X : SwitchModelInputs Φ ι ρ u) : HeightOneSwitchDataPK ι ρ where
  Stage := {c // Reach Φ.next Φ.actual c}
  stage s := X.stage s.1
  quadratic := Φ.quadratic ρ
  sp s := (X.stage s.1).fiberDim ρ
  sm _ := 0
  sign_sum _ _ := add_zero _
  primitiveKernel s := exists_primitiveKernelVector hι ρ (X.stage s.1) (X.class_ne_zero s.1 s.2)
  switch_mixed s _ h1 := by
    obtain ⟨p, hcs, N, -, -⟩ := X.step s.1 s.2 h1
    exact ⟨⟨Φ.next s.1 p, Reach.step p s.2⟩, hcs, fun q => absurd q X.hnq,
      fun _ => ⟨N.toNonquadDims⟩⟩
  switch_single _ q := absurd q X.hnq

/-- **The refined switching data of the inputs, with no DVR** (lane RC0's `HeightOneSwitchDataS`;
`pos` from the nonzero class): the reached configurations, the trivial sign involution, and at each
switch the nonquadratic inputs of its step (duality, detection, the two (5.5a) equations).
Kind: PROVED. -/
def toSwitchDataS (X : SwitchModelInputs Φ ι ρ u) : HeightOneSwitchDataS ι ρ where
  Stage := {c // Reach Φ.next Φ.actual c}
  stage s := X.stage s.1
  quadratic := Φ.quadratic ρ
  sign _ := LinearMap.id
  sign_invol _ _ := LinearMap.id_comp _
  class_ne_zero s h := by
    obtain ⟨i, hi⟩ := X.class_ne_zero s.1 s.2
    exact hi (congrFun h i)
  switch_mixed s _ h1 := by
    obtain ⟨p, hcs, N, -, -⟩ := X.step s.1 s.2 h1
    refine ⟨⟨Φ.next s.1 p, Reach.step p s.2⟩, hcs, fun q => absurd q X.hnq, fun _ => ?_⟩
    exact ⟨N.ε, N.σ, N.J, N.hε, N.hσ, N.hJ2, N.R.U, _, N.hdual, N.hdet,
      N.toNonquadDims.hs, N.toNonquadDims.hs'⟩
  switch_single _ q := absurd q X.hnq

end SwitchModelInputs

/-- **Regularity from the inputs** (tex 4976–5195): over a DVR with residue map `ρ` and `ι`
injective, `∃ a, ι a = u` (through `toSwitchDataPK` and the RC53 group's `regular_of_switchDataPK`).
Kind: PROVED (from the inputs). -/
theorem regular_of_switchModelInputs [IsDomain A] [IsDiscreteValuationRing A]
    (hι : Function.Injective ι) (hρ : ∀ x ∈ maximalIdeal A, ρ x = 0)
    (X : SwitchModelInputs Φ ι ρ u) : ∃ a, ι a = u := by
  obtain ⟨a, ha⟩ := regular_of_switchDataPK hι hρ (X.toSwitchDataPK hι) ⟨Φ.actual, Reach.start⟩
  exact ⟨a, ha.trans X.hu0⟩

/-- **The same regularity with no DVR** (through `toSwitchDataS` and RC16's
`regular_of_switchProcess`): the DVR is used only for the primitive kernel vector. Kind: PROVED
(from the inputs). -/
theorem regular_of_switchModelInputs_noDVR [IsLocalRing A] (hι : Function.Injective ι)
    (hρ : ∀ x ∈ maximalIdeal A, ρ x = 0) (X : SwitchModelInputs Φ ι ρ u) : ∃ a, ι a = u := by
  obtain ⟨a, ha⟩ := ZInQ.Manuscript.RC.Uniform.regular_of_switchProcess
    (Reg := fun x : F => ∃ a, ι a = x)
    (fun x y ⟨a, ha⟩ ⟨b, hb⟩ => ⟨a * b, by rw [map_mul, ha, hb]⟩)
    (X.toSwitchDataS.toProcess hι hρ (fun x : F => ∃ a, ι a = x) (fun a => ⟨a, rfl⟩))
    ⟨Φ.actual, Reach.start⟩
  exact ⟨a, ha.trans X.hu0⟩

end Model

/-! **The inner-limit interface** -/

section InnerLimit

variable (P : Ideal Lambda) [P.IsPrime] {F : Type} [Field F]

/-- **Inner-limit switching inputs with side models** (tex 4391–4451, 4976–5195, 5027–5086): the
frame over `Λ_𝔭` and, at each reached configuration with fiber dimension `> 1`, a successor with a
coordinate step and inner-limit step data (`InnerLimitStepData`: the retained stage complexes and
pairing data, the retained global duality, the residue identity at the derivative label, the
detection, the side-to-stage cohomology isomorphisms), whose limit sides' Selmer complexes are
homotopy equivalent to the fibres of the configuration and of its successor (over `k(𝔭)`; given
the frame, equivalently to the stages' two-term fibre complexes: isomorphic cohomology in every
degree, with no compatibility with the step's maps). Kind: definition (inputs). -/
structure InnerLimitSwitchModel (Φ : SwitchFamily (ResAt P) (Localization.AtPrime P))
    (ι : Localization.AtPrime P →+* F) (u : F) extends SwitchModelFrame Φ ι (resAt P) u where
  /-- The inner-limit switches, with side models. -/
  step : ∀ c, Reach Φ.next Φ.actual c → 1 < (stage c).fiberDim (resAt P) →
    ∃ p : Φ.Prime, Nonempty (CoordStep ι (stage c).u (stage (Φ.next c p)).u) ∧
      ∃ Y : InnerLimitStepData P (stage c) (stage (Φ.next c p)),
        Nonempty (HomotopyEquiv (selCx Y.toStep.SF.Dside).toCC (selCx (Φ.fibre c)).toCC) ∧
        Nonempty (HomotopyEquiv (selCx Y.toStep.SS.Dside).toCC
          (selCx (Φ.fibre (Φ.next c p))).toCC)

variable {P} {Φ : SwitchFamily (ResAt P) (Localization.AtPrime P)}
  {ι : Localization.AtPrime P →+* F} {u : F}

/-- **The model-level inputs of the inner-limit inputs** (each step through
`InnerLimitStepData.toStep`). Kind: PROVED. -/
def InnerLimitSwitchModel.toModelInputs (X : InnerLimitSwitchModel P Φ ι u) :
    SwitchModelInputs Φ ι (resAt P) u where
  toSwitchModelFrame := X.toSwitchModelFrame
  step c hc h1 := by
    obtain ⟨p, hcs, Y, hF, hS⟩ := X.step c hc h1
    exact ⟨p, hcs, Y.toStep, hF, hS⟩

/-- **Regularity from the inner-limit inputs at a height-one prime** (`Λ_𝔭` a DVR, lane RC20's
`isDiscreteValuationRing_atPrime_of_height_one`). Kind: PROVED (from the inputs). -/
theorem regular_of_innerLimitSwitchModel (hP : P.height = 1) (hι : Function.Injective ι)
    (X : InnerLimitSwitchModel P Φ ι u) : ∃ a, ι a = u := by
  have := isDiscreteValuationRing_atPrime_of_height_one P hP
  exact regular_of_switchModelInputs hι (fun _ hx => (IsLocalRing.residue_eq_zero_iff _).2 hx)
    X.toModelInputs

end InnerLimit

/-! **The actual stage inputs with their links, and the leaf-level interface** -/

section Actual

open ZInQ.Manuscript.RC.FibreDuality (lCoordR stageGlobMap)
open ZInQ.Manuscript.RC.Limits (StageA stageMap)
open ZInQ.Contrib.RC53Assist.InnerLimit (splitLocalComplex)
open ZInQ.Manuscript.RC.CoefModules (ActualConj MinS fullAt)
open ZInQ.Manuscript.RC.LambdaCoef (HasFullTwoTorsion)
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Contrib.RC53Assist.InnerLimitArith (MilneLocalFiniteness MilneGlobalFiniteness)

variable {P : Ideal Lambda} [P.IsPrime] {F : Type} [Field F]
  {ι : Localization.AtPrime P →+* F} {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} {Cn : ActualConj K S}
  {W : WeierstrassCurve K} {hW : W.map (Cn.κ : K →+* K) = W}
  [W.IsElliptic] [HasFullTwoTorsion K S W] {Z₀ Z₁ : TwoTermStage ι}

/-- **The retained realization at a stage is the actual stage complex** (tex 4385–4451): a complex
homotopy equivalent to the actual stage Selmer complex, with coordinates in the retained ranks in
which its differential, its localization at the stage prime (through the comparison with the split
model) and its global trace pairing are the stage images of the retained `C.d`, `D.res`, `D.glob`.
Kind: definition (inputs; GLUE). -/
structure RetainedActualStageLink (X : ILStageStepActual P Cn W hW Z₀ Z₁) (i : ℕ) where
  /-- The finite free model of the stage complex. -/
  complex : GCx (StageA i)
  /-- It is homotopy equivalent to the actual stage complex. -/
  model : HomotopyEquiv (actualStageCx W X.hS X.α X.c (hα := X.hα) i).toCC complex.toCC
  /-- Coordinates in the retained ranks. -/
  coord : ∀ n : ℤ, complex.X n ≃ₗ[StageA i] (Fin (X.C.rank n) → StageA i)
  /-- The differential is the stage image of the retained one. -/
  differential : ∀ a b (h : a + 1 = b) (x : complex.X a),
    coord b (complex.d a b h x) = ((X.C.d i a b h).map (stageMap i)) *ᵥ coord a x
  /-- The localization is the stage image of the retained one. -/
  localization : ∀ n (x : complex.X n),
    ((X.D.res n i).map (stageMap i)) *ᵥ coord n x =
      lCoordR (StageA i) n ((actualRes W X.hS X.α X.c (hα := X.hα) X.q X.cmp i).f n n rfl
        ((model.inv.f n).hom x))
  /-- The global trace pairing is the stage image of the retained one. -/
  pairing : ∀ a b (h : a + b = 3) (x : complex.X a) (y : complex.X b),
    coord a x ⬝ᵥ (((X.D.glob a b h i).map (stageMap i)) *ᵥ coord b y) =
      stageGlobMap (X.Q i) (X.tr i) a b h ((model.inv.f a).hom x) ((model.inv.f b).hom y)

variable (P Cn W hW) in
/-- **The inputs of one switch on the actual stage complexes, with their links** (tex 4385–4451,
4834–4907, 5027–5086): `ILStageStepActual` (stage supports `S₀ i ⊆ S_i`, which may grow with the
stage) together with
* `q_old`, `q_full`: the stage prime lies in the stage's old support and carries the full
  condition there (tex 4859–4868), so the stage complex is relaxed at the derivative label;
* `cmp_model`: the comparison of the actual local cochains at the stage prime with the split model
  is a homotopy equivalence (tex 4859–4868);
* `retained_actual`: on a `U`-large set of stages the retained realization is the actual stage
  complex (`RetainedActualStageLink`).
The supports are stage-dependent: the stage primes move with the stage (tex 4834–4907), and with
one finite support `q_old` would confine them to finitely many primes; so the constant-support
form `ILStageStepActualB`, whose rank bounds are discharged, does not carry these links.
Kind: definition (inputs; GLUE). -/
structure ILStageStepLinked (Z₀ Z₁ : TwoTermStage ι) extends
    ILStageStepActual P Cn W hW Z₀ Z₁ where
  /-- The stage prime lies in the old support of its stage. -/
  q_old : ∀ i [NeZero i], q i ∈ S₀ i
  /-- The old condition at the stage prime is the full one. -/
  q_full : ∀ i [NeZero i],
    c i ⟨q i, hS i (q_old i)⟩ (q_old i) =
      fullAt K (Ssel i) (Acoef i) (MinS (hS i) W i (α i)) ⟨q i, hS i (q_old i)⟩
  /-- The comparison with the split model is a homotopy equivalence. -/
  cmp_model : ∀ i [NeZero i], ∃ e : HomotopyEquiv
    (stageLocalCx W hS α (hα := hα) i (q i)).toCC
    (splitLocalComplex (StageA i)).toCC, e.hom = GHom.toCC (cmp i)
  /-- The retained realization is the actual stage complex on a `U`-large set. -/
  retained_actual : ∀ᶠ i in (U : Filter ℕ), ∀ [NeZero i],
    Nonempty (RetainedActualStageLink toILStageStepActual i)

variable (hmloc : MilneLocalFiniteness) (hmglob : MilneGlobalFiniteness)

/-- The inner-limit step data of a linked switch. Kind: definition. -/
abbrev ILStageStepLinked.stepData (X : ILStageStepLinked P Cn W hW Z₀ Z₁) :
    InnerLimitStepData P Z₀ Z₁ :=
  X.toILStageStepActual.toStepData hmloc hmglob

variable (P Cn W hW) in
/-- **Inner-limit switching inputs on the actual stage complexes** (tex 4385–4451, 4976–5195,
5027–5086): the frame over `Λ_𝔭` and, at each reached configuration with fiber dimension `> 1`, a
successor with a coordinate step and a linked switch on the actual stage complexes
(`ILStageStepLinked`) whose limit sides' Selmer complexes are homotopy equivalent to the fibres of
the configuration and of its successor (over `k(𝔭)`; given the frame, equivalently to the stages'
two-term fibre complexes: isomorphic cohomology in every degree, with no compatibility with the
step's maps). Kind: definition (inputs). -/
structure InnerLimitSwitchActual (Φ : SwitchFamily (ResAt P) (Localization.AtPrime P))
    (ι : Localization.AtPrime P →+* F) (u : F) extends SwitchModelFrame Φ ι (resAt P) u where
  /-- The linked switches, with side models. -/
  step : ∀ c, Reach Φ.next Φ.actual c → 1 < (stage c).fiberDim (resAt P) →
    ∃ p : Φ.Prime, Nonempty (CoordStep ι (stage c).u (stage (Φ.next c p)).u) ∧
      ∃ X : ILStageStepLinked P Cn W hW (stage c) (stage (Φ.next c p)),
        Nonempty (HomotopyEquiv (selCx (X.stepData hmloc hmglob).toStep.SF.Dside).toCC
          (selCx (Φ.fibre c)).toCC) ∧
        Nonempty (HomotopyEquiv (selCx (X.stepData hmloc hmglob).toStep.SS.Dside).toCC
          (selCx (Φ.fibre (Φ.next c p))).toCC)

variable {Φ : SwitchFamily (ResAt P) (Localization.AtPrime P)} {u : F}

/-- **The inner-limit inputs of the actual inputs** (each step through its step data). Kind:
PROVED. -/
def InnerLimitSwitchActual.toInner
    (X : InnerLimitSwitchActual P Cn W hW hmloc hmglob Φ ι u) :
    InnerLimitSwitchModel P Φ ι u where
  toSwitchModelFrame := X.toSwitchModelFrame
  step c hc h1 := by
    obtain ⟨p, hcs, Y, hF, hS⟩ := X.step c hc h1
    exact ⟨p, hcs, Y.stepData hmloc hmglob, hF, hS⟩

/-- **Regularity from the actual inputs at a height-one prime**. Kind: PROVED (from the inputs). -/
theorem regular_of_innerLimitSwitchActual (hP : P.height = 1) (hι : Function.Injective ι)
    (X : InnerLimitSwitchActual P Cn W hW hmloc hmglob Φ ι u) : ∃ a, ι a = u :=
  regular_of_innerLimitSwitchModel hP hι (X.toInner hmloc hmglob)

end Actual

end ZInQ.Manuscript.RC.Wiring

import ZInQKernel.Contrib.OneProof.RC.Wiring.GenuineSwitchPK
import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.InnerLimitWiring
import ZInQKernel.Contrib.OneProof.RC.FibreDuality.StageArith

/-!
# Theorem 5.3, Lane RC0 round 11: the height-one regularity leaf on the inner-limit route

Proposition `ex:limits-uniform-lower-bound`, height-one regularity (tex 4976–5200), with the switch
at a derivative label taken on the inner-limit objects (tex 5027–5037, 5055–5086), Lemma
`ex:limits-derivative-switch` (tex 4834–4907) and Lemma `ex:limits-inner-limit` (tex 4385–4451).
The current leaf `PrimRegularityInputsGPK` takes the switches at one fixed characteristic-zero
fibre; there the fixed-fibre step hypotheses cannot hold together for genuine objects (open limit
(3) of `FibreDualityWiring.lean`). The text takes them in the inner limit along moving derivative
labels. This file states a candidate leaf on that route.

**One switch** (`ILStageStep`): at the stages `A_i`, the stage complexes `G i` with flat terms and
finite residual cohomology, a Selmer pairing datum `Q i` whose local complex is the split model at
the derivative label (with a trace `tr i` killing coboundaries), the quasi-isomorphism of its
global duality map, bounded residual cohomology with a uniform rank bound `B`; a retained
realization `C`, `D`, `E` over `Λ` lifting the stage local pairings `tr(0, · ∪ ·)` with the model
ranks the residual ranks; the residue identity at the derivative label (the limit local pairing
is the transported switch pairing with `J = ρ_T(τ)`, `conjMatrix`); the detection `F ≤ U`; and
the side-to-stage isomorphisms. PROVED from it: the inner-limit step data of the RC53 group
(`ILStageStep.toStepData`: `hb11`, `h20` from the residue identity, `J² = 1`), hence a
`QuasiNonquadStep` whose duality is lane RC31's certificate; and the existence of a retained
realization of the stage data (`exists_realization`, lane RC31's producer), so that beyond the
stage data the realization clause adds only the residue identity, the detection and the side
identifications.

**The family** (`ILSwitchInputs`): the RC53 group's `InnerLimitSwitchInputs` with the step data
of each switch given by `ILStageStep`. PROVED: `ILSwitchInputs.toInner`, regularity through
`regular_of_innerLimitSwitchInputs`.

**The leaf** (`PrimRegularityInputsIL`): as `PrimRegularityInputsGPK`, with, at every height-one
prime `𝔭 ≠ (2)` with a nonquadratic specialization, the inner-limit inputs instead of the
fixed-fibre switch data (at a quadratic specialization, tex 5005–5008, the single-sign switches of
`GenuineSwitchDataPK`). PROVED: `primLambdaHalf_of_inputsIL`, `heightOneTarget_of_inputsIL`,
`primRegularityInputs_of_IL` (the consumers of `prim_regular`).

This file keeps the RC53 group's field `primitive` (the actual classes primitive) and abstract
stage complexes. The primitive-kernel form is `InnerLimitRegularityPK.lean`, the inputs of a switch
with the actual stage complexes are `InnerLimitStageActual.lean`, and the candidate leaf combining
both is `PrimRegularityInputsILA` (`InnerLimitRegularityLeaf.lean`).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open CategoryTheory Filter NumberField IsDedekindDomain IsLocalRing
open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.UniformSwitch
open ZInQ.Contrib.CloudB3RC53.SwitchInputs (SwitchFamily Reach InnerLimitStepData
  InnerLimitSwitchInputs regular_of_innerLimitSwitchInputs QuasiNonquadStep fiberH1
  twoTermFiberComplex)
open ZInQ.Manuscript.RC.Rings (isDiscreteValuationRing_atPrime_of_height_one)
open ZInQ.Contrib.RC53Assist.InnerLimit (splitLocalComplex ComplexStages fibreLimitGlobal
  limitRelaxed finiteLimitSide singularLimitSide Vec2)
open ZInQ.Contrib.RC53Assist.InnerLimitArith (ResidualCohomologyFinite)
open ZInQ.Manuscript.RC.FibreDuality (RetainedLimitPairingStages RetainedGlobalDualityStages
  conjMatrix conjMatrix_mul_self transportedPairing transportedPairing_b11
  transportedPairing_b20_bijective localPairingOfMat splitSelData stageLocMat
  exists_retained_of_stageInputs)
open ZInQ.Manuscript.RC.Limits (residualCohomologyAt StageA stageMap stageIdeal)
open ZInQ.Manuscript.RC.Uniform (Lambda finPlane lambdaHalfToFrac
  mem_range_lambdaHalf_iff_forall_height_one)
open ZInQ.Manuscript.RC.CoefModules (ActualConj)
open ZInQ.Manuscript.RC.LambdaCoef (HasFullTwoTorsion)

/-! **One switch on the inner-limit route** -/

section Step

variable (P : Ideal Lambda) [P.IsPrime] {F : Type} [Field F] {ι : Localization.AtPrime P →+* F}
variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (Cn : ActualConj K S) (W : WeierstrassCurve K) (hW : W.map (Cn.κ : K →+* K) = W)
  [W.IsElliptic] [HasFullTwoTorsion K S W]

/-- **The inputs of one switch on the inner-limit route** (tex 4385–4451, 4834–4907, 5027–5086).
Fields (tex; kind):
* `U`, `hU`: the ultrafilter of the inner limit, `U ≤ cofinite` (tex 3298–3300, 5030–5032; data);
* `G`, `hflat`, `hres`: the stage complexes at `A_i` (the stage Selmer complexes), flat terms and
  finite residual cohomology (tex 4391–4414; GLUE identification with the actual stage Selmer
  complexes);
* `Uc`, `res`, `ιc`, `Q`, `tr`, `htr`: the Selmer pairing datum with the split local model
  `D⁰ ⊕ (F ⊕ S)[−1] ⊕ D²[−2]` at the derivative label `q_i` and a trace killing coboundaries
  (tex 4859–4868, 4385–4388; GLUE: its production from the actual local cochains at `q_i` needs
  the local degree-two coordinate `H²(K_{q_i}, M_i) ≅ M_i`);
* `hdual`: the quasi-isomorphism of the global duality map of `Q i` (PRINT: Nekovář, Selmer
  complexes, 5.4.3 at `A_i`, the shape of `stageGlobalDuality`);
* `lo`, `hi`, `hbdd`, `B`, `hB`: bounded residual cohomology and a uniform bound on the residual
  ranks (tex 4400–4406, "a tuple whose model ranks are bounded"; ELLIOT);
* `C`, `D`, `E`, `hlift`, `hrank`, `hrankB`: a retained realization over `Λ` of the stage data
  (data; `exists_realization` proves that one exists from the fields above);
* `ε₀`, `ε₂`, `ε`, `σ`, `hloc`: the residue identity at the derivative label: the limit local
  pairing is the transported switch pairing with `J = ρ_T(τ)` (tex 5027–5037, 2816–2820,
  4888–4890; ELLIOT, with the cup product in tame coordinates);
* `hdet`: the detection `F ≤ U` of the limit relaxed condition (tex 5055–5072; GLUE);
* `φ`, `φ'`: the side-to-stage isomorphisms of the finite and singular limit sides with the fibres
  of the two configurations (tex 5040–5054; GLUE). -/
structure ILStageStep (S₀ S₁ : TwoTermStage ι) where
  /-- The ultrafilter of the inner limit. -/
  U : Ultrafilter ℕ
  hU : (U : Filter ℕ) ≤ cofinite
  /-- The stage complexes. -/
  G : ∀ i, GCx (StageA i)
  hflat : ∀ i n, Module.Flat (StageA i) ((G i).X n)
  /-- The local condition at the derivative label. -/
  Uc : ∀ i, GCx (StageA i)
  /-- The localization into the split local model. -/
  res : ∀ i, GHom (G i) (splitLocalComplex (StageA i))
  /-- The local condition map into the split local model. -/
  ιc : ∀ i, GHom (Uc i) (splitLocalComplex (StageA i))
  /-- The Selmer pairing datum with the split local model. -/
  Q : ∀ i, SelPairData (splitSelData (G i) (res i) (Uc i) (ιc i))
    (splitSelData (G i) (res i) (Uc i) (ιc i))
  /-- The trace. -/
  tr : ∀ i, (coneCx (Q i).resE).X 3 →ₗ[StageA i] StageA i
  htr : ∀ i z, tr i ((coneCx (Q i).resE).d 2 3 rfl z) = 0
  /-- The global duality quasi-isomorphism at the stages. -/
  hdual : ∀ i, QuasiIso (GHom.toCC (globalDualityMap (Q i) (tr i) (htr i)))
  /-- Finite residual cohomology of the stage complexes. -/
  hres : ∀ i [NeZero i], ResidualCohomologyFinite (G i)
  lo : ℤ
  hi : ℤ
  /-- Bounded residual cohomology. -/
  hbdd : ∀ i [NeZero i] (n : ℤ), n < lo ∨ hi < n →
    Module.finrank (ResidueField (StageA i)) (residualCohomologyAt (G i) n) = 0
  /-- The uniform rank bound. -/
  B : ℕ
  hB : ∀ i [NeZero i] (n : ℤ),
    Module.finrank (ResidueField (StageA i)) (residualCohomologyAt (G i) n) ≤ B
  /-- The retained stage complexes. -/
  C : ComplexStages (R := Lambda) stageIdeal U
  /-- The retained pairing data. -/
  D : RetainedLimitPairingStages U C
  /-- The retained global duality. -/
  E : RetainedGlobalDualityStages D
  /-- The retained local pairing lifts the stage local pairings `tr(0, · ∪ ·)`. -/
  hlift : ∀ i, i ≠ 0 → ∀ a b, (D.loc a b i).map (stageMap i) = stageLocMat (Q i) (tr i) a b
  /-- The model ranks are the residual ranks of the stage complexes on a `U`-large set. -/
  hrank : ∀ᶠ i in (U : Filter ℕ), ∀ [NeZero i] (n : ℤ),
    C.rank n = Module.finrank (ResidueField (StageA i)) (residualCohomologyAt (G i) n)
  hrankB : ∀ n, C.rank n ≤ B
  ε₀ : ResAt P
  ε₂ : ResAt P
  ε : ResAt P
  σ : ResAt P
  hε₂ : ε₂ ≠ 0
  hε : ε ≠ 0
  hσ : σ ≠ 0
  /-- The residue identity at the derivative label (tex 5037). -/
  hloc : localPairingOfMat (D.locK P) = transportedPairing ε₀ ε₂ ε σ (conjMatrix Cn W hW P)
  /-- Detection `F ≤ U`. -/
  hdet : finPlane (ResAt P) (Vec2 (ResAt P)) (Vec2 (ResAt P)) ≤
    (limitRelaxed (fibreLimitGlobal U hU P C) (D.resLimit hU P)).U
  /-- The finite side and the stage `S₀`. -/
  φ : (selCx (finiteLimitSide (fibreLimitGlobal U hU P C) (D.resLimit hU P)).Dside).toCC.homology
    1 ≃ₗ[ResAt P] fiberH1 (resAt P) S₀
  /-- The singular side and the stage `S₁`. -/
  φ' : (selCx (singularLimitSide (fibreLimitGlobal U hU P C)
    (D.resLimit hU P)).Dside).toCC.homology 1 ≃ₗ[ResAt P] fiberH1 (resAt P) S₁

variable {P Cn W hW}

/-- **The RC53 group's inner-limit step data from the inputs of one switch**: `J = ρ_T(τ)`
(`conjMatrix`, `J² = 1` by `conjMatrix_mul_self`), and `hb11`, `h20` from the residue identity
(`transportedPairing_b11`, `transportedPairing_b20_bijective`). Kind: PROVED. -/
def ILStageStep.toStepData {S₀ S₁ : TwoTermStage ι} (X : ILStageStep P Cn W hW S₀ S₁) :
    InnerLimitStepData P S₀ S₁ where
  U := X.U
  hU := X.hU
  C := X.C
  D := X.D
  E := X.E
  ε := X.ε
  σ := X.σ
  J := conjMatrix Cn W hW P
  hε := X.hε
  hσ := X.hσ
  hJ := conjMatrix_mul_self Cn W hW P
  hb11 := by
    intro x y
    rw [X.hloc]
    exact transportedPairing_b11 X.ε₀ X.ε₂ X.ε X.σ _ x y
  h20 := by
    rw [X.hloc]
    exact transportedPairing_b20_bijective X.hε₂ X.ε₀ X.ε X.σ (conjMatrix_mul_self Cn W hW P)
  hdet := X.hdet
  φ := X.φ
  φ' := X.φ'

/-- **The stage data have a retained realization** (lane RC31's `exists_retained_of_stageInputs`,
tex 4391–4451): from the stage complexes, the Selmer pairing data with the split local model, the
duality quasi-isomorphisms, the residual finiteness and the rank bounds, there are retained data
`C`, `D`, `E` over `Λ` lifting the stage local pairings, with the model ranks bounded by `B` and
equal to the residual ranks on a `U`-large set. So the realization fields of `ILStageStep` add,
beyond the stage data, only the residue identity, the detection and the side identifications.
Kind: PROVED. -/
theorem exists_realization (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ cofinite)
    (G : ∀ i, GCx (StageA i)) (hflat : ∀ i n, Module.Flat (StageA i) ((G i).X n))
    (Uc : ∀ i, GCx (StageA i)) (res : ∀ i, GHom (G i) (splitLocalComplex (StageA i)))
    (ιc : ∀ i, GHom (Uc i) (splitLocalComplex (StageA i)))
    (Q : ∀ i, SelPairData (splitSelData (G i) (res i) (Uc i) (ιc i))
      (splitSelData (G i) (res i) (Uc i) (ιc i)))
    (tr : ∀ i, (coneCx (Q i).resE).X 3 →ₗ[StageA i] StageA i)
    (htr : ∀ i z, tr i ((coneCx (Q i).resE).d 2 3 rfl z) = 0)
    (hdual : ∀ i, QuasiIso (GHom.toCC (globalDualityMap (Q i) (tr i) (htr i))))
    (hres : ∀ i [NeZero i], ResidualCohomologyFinite (G i)) (lo hi : ℤ)
    (hbdd : ∀ i [NeZero i] (n : ℤ), n < lo ∨ hi < n →
      Module.finrank (ResidueField (StageA i)) (residualCohomologyAt (G i) n) = 0)
    (B : ℕ) (hB : ∀ i [NeZero i] (n : ℤ),
      Module.finrank (ResidueField (StageA i)) (residualCohomologyAt (G i) n) ≤ B) :
    ∃ (C : ComplexStages (R := Lambda) stageIdeal U) (D : RetainedLimitPairingStages U C)
      (_ : RetainedGlobalDualityStages D),
      (∀ i, i ≠ 0 → ∀ a b, (D.loc a b i).map (stageMap i) = stageLocMat (Q i) (tr i) a b) ∧
      (∀ᶠ i in (U : Filter ℕ), ∀ [NeZero i] (n : ℤ),
        C.rank n = Module.finrank (ResidueField (StageA i)) (residualCohomologyAt (G i) n)) ∧
      ∀ n, C.rank n ≤ B := by
  obtain ⟨r₀, C, D, E, hC, -, -, hr₀B, hev, hloc⟩ :=
    exists_retained_of_stageInputs U hU G hflat Uc res ιc Q tr htr hdual hres lo hi hbdd B hB
  refine ⟨C, D, E, hloc, ?_, fun n => hC ▸ hr₀B n⟩
  filter_upwards [hev] with i hi
  intro _ n
  rw [hC]
  exact hi n

end Step

/-! **The family** -/

section Family

variable (P : Ideal Lambda) [P.IsPrime] {F : Type} [Field F]
variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (Cn : ActualConj K S) (W : WeierstrassCurve K) (hW : W.map (Cn.κ : K →+* K) = W)
  [W.IsElliptic] [HasFullTwoTorsion K S W]

/-- **Nonquadratic switching inputs on the inner-limit route** (tex 4976–5195): the RC53 group's
`InnerLimitSwitchInputs` (stage models of the family's fibres, the starting link, nonquadraticity,
primitivity of the stage classes), with the step data of each switch given by `ILStageStep`
(whose sides are the family's fibres). Kind: definition (inputs; fields as at
`InnerLimitSwitchInputs` and `ILStageStep`). -/
structure ILSwitchInputs (Φ : SwitchFamily (ResAt P) (Localization.AtPrime P))
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
  /-- Primitivity of the stage classes. -/
  primitive : ∀ c, Reach Φ.next Φ.actual c → ∃ i, resAt P ((stage c).z i) ≠ 0
  /-- The inner-limit switch steps, with sides the family's fibres. -/
  step : ∀ c, Reach Φ.next Φ.actual c → 1 < (stage c).fiberDim (resAt P) →
    ∃ p : Φ.Prime, Nonempty (CoordStep ι (stage c).u (stage (Φ.next c p)).u) ∧
      ∃ X : ILStageStep P Cn W hW (stage c) (stage (Φ.next c p)),
        X.toStepData.toStep.SF.Dside = Φ.fibre c ∧
          X.toStepData.toStep.SS.Dside = Φ.fibre (Φ.next c p)

variable {P Cn W hW}

/-- **The RC53 group's `InnerLimitSwitchInputs` from the inputs** (`ILStageStep.toStepData` at
each switch). Kind: PROVED. -/
def ILSwitchInputs.toInner {Φ : SwitchFamily (ResAt P) (Localization.AtPrime P)}
    {ι : Localization.AtPrime P →+* F} {u : F} (X : ILSwitchInputs P Cn W hW Φ ι u) :
    InnerLimitSwitchInputs P Φ ι u where
  stage := X.stage
  model := X.model
  hz0 := X.hz0
  hw0 := X.hw0
  hu0 := X.hu0
  hnq := X.hnq
  primitive := X.primitive
  step c hc h1 := by
    obtain ⟨p, hcs, Y, hF, hS⟩ := X.step c hc h1
    exact ⟨p, hcs, Y.toStepData, hF, hS⟩

/-- **Regularity from the inner-limit inputs**: `∃ a, ι a = u` (the RC53 group's
`regular_of_innerLimitSwitchInputs`). Kind: PROVED. -/
theorem regular_of_ILSwitchInputs {Φ : SwitchFamily (ResAt P) (Localization.AtPrime P)}
    {ι : Localization.AtPrime P →+* F} {u : F} (hι : Function.Injective ι)
    (X : ILSwitchInputs P Cn W hW Φ ι u) : ∃ a, ι a = u :=
  regular_of_innerLimitSwitchInputs hι X.toInner

end Family

/-! **The height-one leaf on the inner-limit route** -/

/-- **The height-one regularity inputs on the inner-limit route** (tex 4976–5200). Either `u = 0`
(tex 5196–5197; ELLIOT), or at every height-one prime `𝔭 ≠ (2)` of `Λ` a configuration family `Φ`
over `Λ_𝔭`, genuine at `𝔭` (`IsGenuineFamilyAt`; GLUE), with
* at a nonquadratic specialization: a field `K`, a set of places `S`, the actual conjugation and
  the curve over `K` fixed by it with full two-torsion (data; GLUE identification with the address's
  `K` and `E_K`), and `ILSwitchInputs` over `Φ` starting at `u`;
* at a quadratic specialization (`t̄ (t̄ + 2) = 0`, tex 5005–5008): `GenuineSwitchDataPK` over `Φ`
  (the single-sign switches; fields at `RegularityInputsGPK`).

Kind: definition. -/
def RegularityInputsIL (u : FractionRing Lambda) : Prop :=
  u = 0 ∨ ∀ (P : Ideal Lambda) [P.IsPrime], P.height = 1 → P ≠ Ideal.span {2} →
    ∃ Φ : SwitchFamily (ResAt P) (Localization.AtPrime P), IsGenuineFamilyAt P Φ ∧
      ((∃ (K : Type) (_ : Field K) (_ : NumberField K) (S : Set (HeightOneSpectrum (𝓞 K)))
          (Cn : ActualConj K S) (W : WeierstrassCurve K) (hW : W.map (Cn.κ : K →+* K) = W)
          (_ : W.IsElliptic) (_ : HasFullTwoTorsion K S W),
          Nonempty (ILSwitchInputs P Cn W hW Φ (UniformSwitch.toFracAt P) u)) ∨
        (Φ.quadratic (resAt P) ∧
          Nonempty (GenuineSwitchDataPK Φ (UniformSwitch.toFracAt P) (resAt P) u)))

/-- **`u ∈ Λ[1/2]` from the inner-limit inputs**: at every height-one prime `𝔭 ≠ (2)`, `u ∈ ι(Λ_𝔭)`
by `regular_of_ILSwitchInputs` (nonquadratic) or `regular_of_genuineSwitchDataPK` over the DVR
`Λ_𝔭` (quadratic); then the intersection formula (tex 5190–5194). Kind: PROVED from the inputs. -/
theorem RegularityInputsIL.mem_lambdaHalf {u : FractionRing Lambda} (h : RegularityInputsIL u) :
    u ∈ lambdaHalfToFrac.range := by
  rw [mem_range_lambdaHalf_iff_forall_height_one]
  intro P _ hP hne
  rcases h with rfl | h
  · exact Subalgebra.zero_mem _
  · obtain ⟨Φ, -, hΦ⟩ := h P hP hne
    rcases hΦ with ⟨K, _, _, S, Cn, W, hW, _, _, ⟨X⟩⟩ | ⟨-, ⟨G⟩⟩
    · obtain ⟨a, ha⟩ := regular_of_ILSwitchInputs (UniformSwitch.toFracAt_injective P) X
      rw [← ha]
      exact ⟨a, rfl⟩
    · have := isDiscreteValuationRing_atPrime_of_height_one P hP
      obtain ⟨a, ha⟩ := regular_of_genuineSwitchDataPK (UniformSwitch.toFracAt_injective P)
        (fun _ hx => (IsLocalRing.residue_eq_zero_iff _).2 hx) G
      rw [← ha]
      exact ⟨a, rfl⟩

section HeightOneTarget

variable {ℓ : ℕ} (D : RCData ℓ)

/-- **The height-one leaf on the inner-limit route** (tex 4976–5200, at the ring instances of the
final field): for every final family `F` and every address `x` there is `u ∈ Frac Λ` with
`IsTExpansion u (D.uPrim F x)` (tex 3877–3892; GLUE) and `RegularityInputsIL u`.
Kind: definition. -/
def PrimRegularityInputsIL : Prop :=
  ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b,
    ∃ u : FractionRing Lambda, IsTExpansion u (D.uPrim F x) ∧ RegularityInputsIL u

/-- **`u_{prim,x} ∈ Λ[1/2]`** at every address of every final family. Kind: PROVED. -/
theorem primLambdaHalf_of_inputsIL (h : PrimRegularityInputsIL D) :
    ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b,
      InLamHalf (D.uPrim F x) := by
  intro Co Ce F hF x
  obtain ⟨u, hT, hreg⟩ := h Co Ce F hF x
  exact inLamHalf_of_isTExpansion hT hreg.mem_lambdaHalf

/-- **`RCSteps.height_one`** from the leaf and (4.7). Kind: PROVED from the inputs. -/
theorem heightOneTarget_of_inputsIL (h : PrimRegularityInputsIL D)
    (h47 : CommonCoordinateTarget D) : HeightOneTarget D :=
  heightOneTarget_of_prim D (primLambdaHalf_of_inputsIL D h) h47

/-- **The old leaf `PrimRegularityInputs D`** (the form consumed by the base-zero step), from the
leaf. Kind: PROVED. -/
theorem primRegularityInputs_of_IL (h : PrimRegularityInputsIL D) : PrimRegularityInputs D :=
  primRegularityInputs_of_S D ((primRegularityInputsS_iff D).mpr (primLambdaHalf_of_inputsIL D h))

end HeightOneTarget

end ZInQ.Manuscript.RC.Wiring

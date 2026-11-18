import ZInQKernel.Contrib.OneProof.RC.Wiring.InnerLimitRegularityPK
import ZInQKernel.Contrib.OneProof.RC.Wiring.InnerLimitStageActual

/-!
# Theorem 5.3, Lane RC0 round 11: the candidate height-one leaf on the inner-limit route

Proposition `ex:limits-uniform-lower-bound`, height-one regularity (tex 4976–5200), with the switch
at a derivative label on the inner-limit objects (tex 5027–5086, 4834–4907, 4385–4451). The
candidate leaf `PrimRegularityInputsILA` combines:

* the family inputs in the primitive-kernel form (`ILSwitchInputsPK`, `InnerLimitRegularityPK.lean`:
  the actual classes nonzero, the primitive kernel vectors PROVED over the DVR `Λ_𝔭`);
* the inputs of each switch with the actual stage complexes (`ILStageStepActual`,
  `InnerLimitStageActual.lean`: the actual stage Selmer complexes, their flat terms and finite
  residual cohomology PROVED from the old conditions and the two finiteness PRINTs, Milne I.2.3 and
  I.4.10; the localization at the stage prime followed by a comparison with the split model);
* at a quadratic specialization (tex 5005–5008), the single-sign switches of
  `GenuineSwitchDataPK`, as in the current leaf.

PROVED: `ILSwitchInputsA.toPK`, `RegularityInputsILA.toPK`, `PrimRegularityInputsILA.toPK`, and the
consumers of `prim_regular`: `primLambdaHalf_of_inputsILA`, `heightOneTarget_of_inputsILA`,
`primRegularityInputs_of_ILA`; the degenerate satisfiability `primRegularityInputsILA_of_uPrim_zero`
(vanishing primitive coordinates, given the two PRINTs).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open CategoryTheory Filter NumberField IsDedekindDomain IsLocalRing
open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.UniformSwitch
open ZInQ.Contrib.CloudB3RC53.SwitchInputs (SwitchFamily Reach twoTermFiberComplex)
open ZInQ.Contrib.RC53Assist.InnerLimitArith (MilneLocalFiniteness MilneGlobalFiniteness)
open ZInQ.Manuscript.RC.Uniform (Lambda)
open ZInQ.Manuscript.RC.CoefModules (ActualConj)
open ZInQ.Manuscript.RC.LambdaCoef (HasFullTwoTorsion)

/-! **The family with the actual stage complexes** -/

section Family

variable (hmloc : MilneLocalFiniteness) (hmglob : MilneGlobalFiniteness)
variable (P : Ideal Lambda) [P.IsPrime] {F : Type} [Field F]
variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (Cn : ActualConj K S) (W : WeierstrassCurve K) (hW : W.map (Cn.κ : K →+* K) = W)
  [W.IsElliptic] [HasFullTwoTorsion K S W]

/-- **Nonquadratic switching inputs on the inner-limit route, with the actual stage complexes**
(tex 4976–5195): the fields of `ILSwitchInputsPK` (stage models of the family's fibres, the
starting link, nonquadraticity, the actual classes nonzero), with the inputs of each switch given
by `ILStageStepActual` (whose sides are the family's fibres). Kind: definition (inputs; fields as
at `ILSwitchInputsPK` and `ILStageStepActual`). -/
structure ILSwitchInputsA (Φ : SwitchFamily (ResAt P) (Localization.AtPrime P))
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
  /-- The actual class of every reached configuration is nonzero (tex 4992, 5137–5144). -/
  class_ne_zero : ∀ c, Reach Φ.next Φ.actual c → ∃ i, (stage c).z i ≠ 0
  /-- The inner-limit switch steps, with the actual stage complexes and sides the family's
  fibres. -/
  step : ∀ c, Reach Φ.next Φ.actual c → 1 < (stage c).fiberDim (resAt P) →
    ∃ p : Φ.Prime, Nonempty (CoordStep ι (stage c).u (stage (Φ.next c p)).u) ∧
      ∃ X : ILStageStepActual P Cn W hW (stage c) (stage (Φ.next c p)),
        (X.toStepData hmloc hmglob).toStep.SF.Dside = Φ.fibre c ∧
          (X.toStepData hmloc hmglob).toStep.SS.Dside = Φ.fibre (Φ.next c p)

variable {hmloc hmglob P Cn W hW}

/-- **`ILSwitchInputsPK` from the inputs with the actual stage complexes**
(`ILStageStepActual.toILStageStep` at each switch). Kind: PROVED. -/
def ILSwitchInputsA.toPK {Φ : SwitchFamily (ResAt P) (Localization.AtPrime P)}
    {ι : Localization.AtPrime P →+* F} {u : F}
    (X : ILSwitchInputsA hmloc hmglob P Cn W hW Φ ι u) :
    ILSwitchInputsPK P Cn W hW Φ ι u where
  stage := X.stage
  model := X.model
  hz0 := X.hz0
  hw0 := X.hw0
  hu0 := X.hu0
  hnq := X.hnq
  class_ne_zero := X.class_ne_zero
  step c hc h1 := by
    obtain ⟨p, hcs, Y, hF, hS⟩ := X.step c hc h1
    exact ⟨p, hcs, Y.toILStageStep hmloc hmglob, hF, hS⟩

end Family

/-! **The candidate leaf** -/

/-- **The height-one regularity inputs on the inner-limit route, with the actual stage complexes**
(tex 4976–5200). Either `u = 0` (tex 5196–5197; ELLIOT), or at every height-one prime `𝔭 ≠ (2)` of
`Λ` a configuration family `Φ` over `Λ_𝔭`, genuine at `𝔭` (`IsGenuineFamilyAt`; GLUE), with
* at a nonquadratic specialization: a field `K`, a set of places `S`, the actual conjugation and
  the curve over `K` fixed by it with full two-torsion (data; GLUE identification with the address's
  `K` and `E_K`), and `ILSwitchInputsA` over `Φ` starting at `u`;
* at a quadratic specialization (tex 5005–5008): `GenuineSwitchDataPK` over `Φ`.

Kind: definition. -/
def RegularityInputsILA (hmloc : MilneLocalFiniteness) (hmglob : MilneGlobalFiniteness)
    (u : FractionRing Lambda) : Prop :=
  u = 0 ∨ ∀ (P : Ideal Lambda) [P.IsPrime], P.height = 1 → P ≠ Ideal.span {2} →
    ∃ Φ : SwitchFamily (ResAt P) (Localization.AtPrime P), IsGenuineFamilyAt P Φ ∧
      ((∃ (K : Type) (_ : Field K) (_ : NumberField K) (S : Set (HeightOneSpectrum (𝓞 K)))
          (Cn : ActualConj K S) (W : WeierstrassCurve K) (hW : W.map (Cn.κ : K →+* K) = W)
          (_ : W.IsElliptic) (_ : HasFullTwoTorsion K S W),
          Nonempty (ILSwitchInputsA hmloc hmglob P Cn W hW Φ (UniformSwitch.toFracAt P) u)) ∨
        (Φ.quadratic (resAt P) ∧
          Nonempty (GenuineSwitchDataPK Φ (UniformSwitch.toFracAt P) (resAt P) u)))

/-- The inputs give `RegularityInputsILPK` (`ILSwitchInputsA.toPK`). Kind: PROVED. -/
theorem RegularityInputsILA.toPK {hmloc : MilneLocalFiniteness} {hmglob : MilneGlobalFiniteness}
    {u : FractionRing Lambda} (h : RegularityInputsILA hmloc hmglob u) :
    RegularityInputsILPK u := by
  rcases h with h | h
  · exact Or.inl h
  · refine Or.inr fun P _ hP hne => ?_
    obtain ⟨Φ, hΦ, hb⟩ := h P hP hne
    refine ⟨Φ, hΦ, ?_⟩
    rcases hb with ⟨K, _, _, S, Cn, W, hW, _, _, ⟨X⟩⟩ | hq
    · exact Or.inl ⟨K, inferInstance, inferInstance, S, Cn, W, hW, inferInstance, inferInstance,
        ⟨X.toPK⟩⟩
    · exact Or.inr hq

section HeightOneTarget

variable {ℓ : ℕ} (D : RCData ℓ)

/-- **The candidate height-one leaf on the inner-limit route** (tex 4976–5200, at the ring
instances of the final field): the two finiteness PRINTs (Milne, Arithmetic duality theorems,
I.2.3 and I.4.10), and for every final family `F` and every address `x` some `u ∈ Frac Λ` with
`IsTExpansion u (D.uPrim F x)` (tex 3877–3892; GLUE) and `RegularityInputsILA u`.
Kind: definition. -/
def PrimRegularityInputsILA : Prop :=
  ∃ (hmloc : MilneLocalFiniteness) (hmglob : MilneGlobalFiniteness),
    ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b,
      ∃ u : FractionRing Lambda, IsTExpansion u (D.uPrim F x) ∧ RegularityInputsILA hmloc hmglob u

/-- The candidate leaf gives `PrimRegularityInputsILPK`. Kind: PROVED. -/
theorem PrimRegularityInputsILA.toPK (h : PrimRegularityInputsILA D) :
    PrimRegularityInputsILPK D := by
  obtain ⟨_, _, h⟩ := h
  intro Co Ce F hF x
  obtain ⟨u, hT, hreg⟩ := h Co Ce F hF x
  exact ⟨u, hT, hreg.toPK⟩

/-- **`u_{prim,x} ∈ Λ[1/2]`** at every address of every final family, from the candidate leaf.
Kind: PROVED from the inputs. -/
theorem primLambdaHalf_of_inputsILA (h : PrimRegularityInputsILA D) :
    ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b,
      InLamHalf (D.uPrim F x) :=
  primLambdaHalf_of_inputsILPK D h.toPK

/-- **`RCSteps.height_one`** from the candidate leaf and (4.7). Kind: PROVED from the inputs. -/
theorem heightOneTarget_of_inputsILA (h : PrimRegularityInputsILA D)
    (h47 : CommonCoordinateTarget D) : HeightOneTarget D :=
  heightOneTarget_of_inputsILPK D h.toPK h47

/-- **The old leaf `PrimRegularityInputs D`** (the form consumed by the base-zero step), from the
candidate leaf. Kind: PROVED. -/
theorem primRegularityInputs_of_ILA (h : PrimRegularityInputsILA D) : PrimRegularityInputs D :=
  primRegularityInputs_of_ILPK D h.toPK

/-- **The candidate leaf and the current one feed the same consumer**: each gives
`PrimRegularityInputsS D` (`u_{prim,x} ∈ Λ[1/2]` everywhere). Kind: PROVED. -/
theorem primRegularityInputsS_of_ILA_or_GPK
    (h : PrimRegularityInputsILA D ∨ PrimRegularityInputsGPK D) : PrimRegularityInputsS D := by
  rcases h with h | h
  · exact primRegularityInputsS_of_ILPK D h.toPK
  · exact primRegularityInputsS_of_GPK D h

/-- **Degenerate satisfiability**: given the two PRINTs, the candidate leaf holds when the
primitive coordinates vanish (the `u = 0` branch). Kind: PROVED. -/
theorem primRegularityInputsILA_of_uPrim_zero (hmloc : MilneLocalFiniteness)
    (hmglob : MilneGlobalFiniteness) (hD : ∀ F x, D.uPrim F x = 0) : PrimRegularityInputsILA D :=
  ⟨hmloc, hmglob, fun _ _ F _ x => ⟨0, by rw [hD F x]; exact isTExpansion_zero, Or.inl rfl⟩⟩

end HeightOneTarget

end ZInQ.Manuscript.RC.Wiring

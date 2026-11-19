import ZInQKernel.Contrib.OneProof.RC.Wiring.InnerLimitFamilyPin
import ZInQKernel.Contrib.OneProof.RC.Wiring.InnerLimitAddressPinTerminal

/-!
**Theorem 5.3, Lane RC0: the collapse of the pinned clause over the family's moving character is
exactly the terminal case**

Proposition `ex:limits-uniform-lower-bound`, height-one regularity (tex 4976–5200), at a fixed
address family `A : AddressMovingFamilyR Ψ h W` over the family's moving character and a fixed
retained limit `L` of `A.Fam` (the clause `PinnedLimitAt`). The switching argument stops at fibre
dimension one: "After cancellation the terminal complex has one free generator in each of degrees
one and two; its differential is zero because its generic kernel has rank one" (tex 5154–5161).
`PinnedLimitAt.terminal_of_stationary_family` (`Wiring/InnerLimitFamilyPinFix.lean`) and
`InnerLimitSwitchPinnedOn.terminal_of_stationary` below show that a configuration family without
proper successors forces `dim H¹ = 1` of the finite fibre of `L`. This file proves the converse,
with the terminal family, the finite-fibre model and the quadratic-branch data of
`InnerLimitAddressPinTerminal` reused unchanged.

* `terminalPinnedOn` (with `terminalPinnedOn_stage`): the linked-switch inputs on the label
  families of any base family over the terminal family, whose stage is the stage of the integral
  model `Dfin` at every configuration; the step field is vacuous at fibre dimension one.
* `InnerLimitSwitchPinnedOn.nonquadraticAt`, `InnerLimitSwitchPinnedOn.terminal_of_stationary`
  (PROVED): such inputs over a genuine family live at nonquadratic primes (tex 5004–5008), and
  over a stationary family pinned to a finite fibre they force `dim H¹ = 1` of that fibre.
* `pinnedLimitAt_of_terminal` (PROVED): the clause `PinnedLimitAt Cn hW A L u 𝔭` at a height-one
  prime from an integral model `Dfin` of the finite side of `L` with nonzero class and coordinate
  `u`, a genuine realization of the finite fibre and `dim H¹ = 1`: through `terminalPinnedOn` on
  the label families of `A.Fam` at a nonquadratic prime, through `terminalHomology` at a
  quadratic one.
* `collapse_iff_terminal_on`, `collapse_iff_terminal_on_of_nonquadratic` (PROVED): a genuine
  stationary family pinned to the finite fibre of `L`, with linked-switch inputs on the label
  families of `A.Fam` whose actual stage is the stage of `Dfin`, exists if and only if `𝔭` is
  nonquadratic, `dim H¹ = 1` for the finite fibre, the finite fibre has a genuine realization and
  the class of `Dfin` is nonzero (and `u` is the coordinate of `Dfin`).

As for `InnerLimitSwitchPinned`, the frame of `InnerLimitSwitchPinnedOn` asks `¬ Φ.quadratic`,
which for a genuine family fails at `𝔭 = (X)` and `𝔭 = (X + 2)` (tex 5004–5008); there the
clause is met through its quadratic branch.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open CategoryTheory NumberField IsDedekindDomain Module
open ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Contrib.CloudB3RC53
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.UniformSwitch
open ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Manuscript.RC.Uniform (Lambda)
open ZInQ.Manuscript.RC.Limits (stageIdeal_tendsToZero)
open ZInQ.Manuscript.RC.CoefModules (ActualConj)
open ZInQ.Manuscript.RC.LambdaCoef (HasFullTwoTorsion)
open ZInQ.Contrib.RC53Assist.InnerLimitMoving (IntegralMatrixStageData selmerStages
  derivativeDiagram retainedRestrictionStages)
open scoped PowerSeries.WithPiTopology

section TerminalOn

variable {P : Ideal Lambda} [P.IsPrime] {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} {W : WeierstrassCurve K} [W.IsElliptic]
  [HasFullTwoTorsion K S W] {Fam : MovingStageFamily W}

/-- **The linked-switch inputs on a base family in the terminal case** (tex 4976–4996,
5154–5161): over the terminal family, at a nonquadratic prime, with nonzero class of `Dfin` and
`dim H¹ = 1` of the finite fibre of `L`, inputs on the label families of the base family `Fam₀`
whose stage is `Dfin.stage` at every configuration, with model `e` followed by
`finiteFibreModel` and starting coordinate the coordinate of `Dfin` (as `terminalPinned`); the
step field is vacuous since the fibre dimension is one (`fiberDim_finiteStage`). Kind: PROVED. -/
def terminalPinnedOn (Cn : ActualConj K S) (hW : W.map (Cn.κ : K →+* K) = W) (ℓ : ℕ)
    (h : ℤ) (Fam₀ : MovingStageFamily W) (L : MovingRetainedLimit Fam)
    (Dfin : IntegralMatrixStageData stageIdeal_tendsToZero L.hU
      (algebraMap Lambda (Localization.AtPrime P)) (UniformSwitch.toFracAt P)
      (selmerStages (derivativeDiagram L.C (retainedRestrictionStages L.D) .finite)))
    (G : SelData (ResAt P)) (e : HomotopyEquiv (selCx G).toCC (L.finiteFibre P).toCC)
    (hnq : NonquadraticAt P) (hz : ∃ i, Dfin.stage.z i ≠ 0)
    (hdim : finrank (ResAt P) ((L.finiteFibre P).toCC.homology 1) = 1) :
    InnerLimitSwitchPinnedOn P Cn hW ℓ h Fam₀ (terminalFamily L Dfin G e)
      (UniformSwitch.toFracAt P) Dfin.stage.u where
  toSwitchModelFrame := stageCollapseFrame G (L.finiteStage_residue_zero Dfin)
    (e.trans (L.finiteFibreModel Dfin)) hnq hz
  step _ _ h1 :=
    absurd (h1.trans_eq ((L.fiberDim_finiteStage Dfin).trans hdim)) (lt_irrefl 1)

/-- The stage of the terminal inputs on a base family is `Dfin.stage` at every configuration
(tex 4986–4992). Kind: PROVED. -/
theorem terminalPinnedOn_stage (Cn : ActualConj K S) (hW : W.map (Cn.κ : K →+* K) = W)
    (ℓ : ℕ) (h : ℤ) (Fam₀ : MovingStageFamily W) (L : MovingRetainedLimit Fam)
    (Dfin : IntegralMatrixStageData stageIdeal_tendsToZero L.hU
      (algebraMap Lambda (Localization.AtPrime P)) (UniformSwitch.toFracAt P)
      (selmerStages (derivativeDiagram L.C (retainedRestrictionStages L.D) .finite)))
    (G : SelData (ResAt P)) (e : HomotopyEquiv (selCx G).toCC (L.finiteFibre P).toCC)
    (hnq : NonquadraticAt P) (hz : ∃ i, Dfin.stage.z i ≠ 0)
    (hdim : finrank (ResAt P) ((L.finiteFibre P).toCC.homology 1) = 1)
    (c : (terminalFamily L Dfin G e).Config) :
    (terminalPinnedOn Cn hW ℓ h Fam₀ L Dfin G e hnq hz hdim).stage c = Dfin.stage :=
  rfl

end TerminalOn

section PinnedOn

variable {P : Ideal Lambda} [P.IsPrime] {F : Type} [Field F] {K : Type} [Field K]
  [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))} {Cn : ActualConj K S}
  {W : WeierstrassCurve K} {hW : W.map (Cn.κ : K →+* K) = W} [W.IsElliptic]
  [HasFullTwoTorsion K S W] {ℓ : ℕ} {h : ℤ} {Fam₀ : MovingStageFamily W}
  {Φ : SwitchFamily (ResAt P) (Localization.AtPrime P)} {ι : Localization.AtPrime P →+* F}
  {u : F}

/-- **Inputs on a base family over a genuine family force a nonquadratic prime** (tex
4997–5008): their frame asks `¬ Φ.quadratic`, which for a genuine family is `NonquadraticAt`;
so at a prime containing `X` or `X + 2` there are none (`not_nonquadraticAt_of_mem`).
Kind: PROVED. -/
theorem InnerLimitSwitchPinnedOn.nonquadraticAt
    (X : InnerLimitSwitchPinnedOn P Cn hW ℓ h Fam₀ Φ ι u) (hΦ : IsGenuineFamilyAt P Φ) :
    NonquadraticAt P :=
  hΦ.not_quadratic_iff.mp X.hnq

/-- **A stationary family forces the terminal case for inputs on a base family** (tex
4986–4992, 5154–5161): for such inputs at a height-one prime over a family without proper
successors whose actual fibre is homotopy equivalent to the finite fibre of a retained limit `L`,
that fibre has `dim H¹ = 1` (`fiberDim_eq_pinned`, `fiberDim_eq_one_of_stationary`).
Kind: PROVED. -/
theorem InnerLimitSwitchPinnedOn.terminal_of_stationary (hP : P.height = 1)
    {v : FractionRing Lambda}
    (X : InnerLimitSwitchPinnedOn P Cn hW ℓ h Fam₀ Φ (UniformSwitch.toFracAt P) v)
    {Fam : MovingStageFamily W} (L : MovingRetainedLimit Fam)
    (e : HomotopyEquiv (selCx (Φ.fibre Φ.actual)).toCC (L.finiteFibre P).toCC)
    (hstat : ∀ c p, Φ.next c p = c) :
    finrank (ResAt P) ((L.finiteFibre P).toCC.homology 1) = 1 :=
  (X.fiberDim_eq_pinned _ e).symm.trans
    (X.fiberDim_eq_one_of_stationary hP (UniformSwitch.toFracAt_injective P) hstat)

end PinnedOn

section Clause

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (Cn : ActualConj K S) {W : WeierstrassCurve K} (hW : W.map (Cn.κ : K →+* K) = W)
  [W.IsElliptic] [HasFullTwoTorsion K S W] {ℓ : ℕ} {Q : Finset ℕ}
  {Ψ : FamilyMovingCharacter K ℓ Q} {h : ℤ}

/-- **The pinned clause at a height-one prime from the terminal data** (tex 4976–5200,
5154–5161): for the address's moving family `A` over the family's character, a retained limit
`L` of `A.Fam`, an integral model `Dfin` of its finite side at `𝔭` with nonzero class and
coordinate `u`, a genuine realization `G` of the finite fibre (`e`) and `dim H¹ = 1` of the
finite fibre, `PinnedLimitAt Cn hW A L u 𝔭` holds: the terminal family is genuine and pinned by
`e`; at a nonquadratic prime through `terminalPinnedOn` on the label families of `A.Fam`, at a
quadratic one (tex 5004–5008) through the homology-level data `terminalHomology`.
Kind: PROVED. -/
theorem pinnedLimitAt_of_terminal {P : Ideal Lambda} [P.IsPrime] (hP : P.height = 1)
    {u : FractionRing Lambda} (A : AddressMovingFamilyR Ψ h W) (L : MovingRetainedLimit A.Fam)
    (Dfin : IntegralMatrixStageData stageIdeal_tendsToZero L.hU
      (algebraMap Lambda (Localization.AtPrime P)) (UniformSwitch.toFracAt P)
      (selmerStages (derivativeDiagram L.C (retainedRestrictionStages L.D) .finite)))
    (G : SelData (ResAt P)) (hG : IsGaloisSelData G)
    (e : HomotopyEquiv (selCx G).toCC (L.finiteFibre P).toCC) (hz : ∃ i, Dfin.stage.z i ≠ 0)
    (hdim : finrank (ResAt P) ((L.finiteFibre P).toCC.homology 1) = 1)
    (hu : Dfin.stage.u = u) : PinnedLimitAt Cn hW A L u P := by
  subst hu
  refine ⟨terminalFamily L Dfin G e, terminalFamily_isGenuine L Dfin hG e, Dfin, ⟨e⟩, ?_⟩
  by_cases hq : (terminalFamily L Dfin G e).quadratic (resAt P)
  · exact Or.inr ⟨hq, terminalHomology hP L Dfin G e hz hdim, rfl⟩
  · exact Or.inl ⟨terminalPinnedOn Cn hW ℓ h A.Fam L Dfin G e
      ((terminalFamily_not_quadratic_iff L Dfin G e).mp hq) hz hdim, rfl⟩

/-- **The collapse over the family's character is exactly the terminal case** (tex 4976–5008,
5154–5161): at a height-one prime, for the address's moving family `A` over the family's
character, a retained limit `L` of `A.Fam` and an integral model `Dfin` of its finite side, there
is a family genuine at `𝔭`, stationary, with its actual fibre homotopy equivalent to the finite
fibre of `L` and with linked-switch inputs on the label families of `A.Fam` starting at `u`
whose actual stage is `Dfin.stage`, if and only if `𝔭` is nonquadratic, `dim H¹ = 1` for the
finite fibre, the finite fibre has a genuine realization, the class of `Dfin` is nonzero and `u`
is the coordinate of `Dfin`. Forward: `terminal_of_stationary`, `class_ne_zero`, `hnq`, `hu0`;
backward: `terminalPinnedOn`. Kind: PROVED. -/
theorem collapse_iff_terminal_on {P : Ideal Lambda} [P.IsPrime] (hP : P.height = 1)
    {u : FractionRing Lambda} (A : AddressMovingFamilyR Ψ h W) (L : MovingRetainedLimit A.Fam)
    (Dfin : IntegralMatrixStageData stageIdeal_tendsToZero L.hU
      (algebraMap Lambda (Localization.AtPrime P)) (UniformSwitch.toFracAt P)
      (selmerStages (derivativeDiagram L.C (retainedRestrictionStages L.D) .finite))) :
    (∃ Φ : SwitchFamily (ResAt P) (Localization.AtPrime P), IsGenuineFamilyAt P Φ ∧
      (∀ c p, Φ.next c p = c) ∧
      Nonempty (HomotopyEquiv (selCx (Φ.fibre Φ.actual)).toCC (L.finiteFibre P).toCC) ∧
      ∃ X : InnerLimitSwitchPinnedOn P Cn hW ℓ h A.Fam Φ (UniformSwitch.toFracAt P) u,
        X.stage Φ.actual = Dfin.stage) ↔
    NonquadraticAt P ∧ finrank (ResAt P) ((L.finiteFibre P).toCC.homology 1) = 1 ∧
      (∃ G : SelData (ResAt P), IsGaloisSelData G ∧
        Nonempty (HomotopyEquiv (selCx G).toCC (L.finiteFibre P).toCC)) ∧
      (∃ i, Dfin.stage.z i ≠ 0) ∧ Dfin.stage.u = u := by
  constructor
  · rintro ⟨Φ, hΦ, hstat, ⟨e⟩, X, hX⟩
    refine ⟨X.nonquadraticAt hΦ, X.terminal_of_stationary hP L e hstat,
      ⟨Φ.fibre Φ.actual, hΦ.1 Φ.actual, ⟨e⟩⟩, ?_, ?_⟩
    · rw [← hX]
      exact X.class_ne_zero Φ.actual Reach.start
    · rw [← hX]
      exact X.hu0
  · rintro ⟨hnq, hdim, ⟨G, hG, ⟨e⟩⟩, hz, rfl⟩
    exact ⟨terminalFamily L Dfin G e, terminalFamily_isGenuine L Dfin hG e,
      terminalFamily_next L Dfin G e, ⟨e⟩,
      terminalPinnedOn Cn hW ℓ h A.Fam L Dfin G e hnq hz hdim, rfl⟩

/-- **The collapse over the family's character at a nonquadratic prime** (tex 4976–5008,
5154–5161), with inputs on the label families of `A.Fam` starting at the coordinate of `Dfin`: a
genuine stationary family with the pin and such inputs exists if and only if `dim H¹ = 1` for the
finite fibre, the finite fibre has a genuine realization and the class of `Dfin` is nonzero.
Kind: PROVED. -/
theorem collapse_iff_terminal_on_of_nonquadratic {P : Ideal Lambda} [P.IsPrime]
    (hP : P.height = 1) (hnq : NonquadraticAt P) (A : AddressMovingFamilyR Ψ h W)
    (L : MovingRetainedLimit A.Fam)
    (Dfin : IntegralMatrixStageData stageIdeal_tendsToZero L.hU
      (algebraMap Lambda (Localization.AtPrime P)) (UniformSwitch.toFracAt P)
      (selmerStages (derivativeDiagram L.C (retainedRestrictionStages L.D) .finite))) :
    (∃ Φ : SwitchFamily (ResAt P) (Localization.AtPrime P), IsGenuineFamilyAt P Φ ∧
      (∀ c p, Φ.next c p = c) ∧
      Nonempty (HomotopyEquiv (selCx (Φ.fibre Φ.actual)).toCC (L.finiteFibre P).toCC) ∧
      ∃ X : InnerLimitSwitchPinnedOn P Cn hW ℓ h A.Fam Φ (UniformSwitch.toFracAt P)
          Dfin.stage.u,
        X.stage Φ.actual = Dfin.stage) ↔
    finrank (ResAt P) ((L.finiteFibre P).toCC.homology 1) = 1 ∧
      (∃ G : SelData (ResAt P), IsGaloisSelData G ∧
        Nonempty (HomotopyEquiv (selCx G).toCC (L.finiteFibre P).toCC)) ∧
      ∃ i, Dfin.stage.z i ≠ 0 :=
  (collapse_iff_terminal_on Cn hW hP A L Dfin).trans
    ⟨fun ⟨_, h1, h2, h3, _⟩ => ⟨h1, h2, h3⟩,
      fun ⟨h1, h2, h3⟩ => ⟨hnq, h1, h2, h3, rfl⟩⟩

end Clause

end ZInQ.Manuscript.RC.Wiring

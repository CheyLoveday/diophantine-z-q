import ZInQKernel.Contrib.OneProof.RC.Wiring.InnerLimitFamilyPin

/-!
# Theorem 5.3, Lane RC0 round 20: the collapse of the pinned clause for its own configuration family

Proposition `ex:limits-uniform-lower-bound`, height-one regularity (tex 4976–5200). The pinned
clause `PinnedLimitAt` (`Wiring/InnerLimitFamilyPin.lean`) asks at each height-one prime for a
configuration family `Φ`, the pin of its actual fibre to the finite fibre of the address's fixed
limit `L`, and either branch's data over `Φ`. The earlier statement
`PinnedLimitAt.terminal_of_stationary` assumes that every configuration family is stationary, a
hypothesis no instance satisfies (a family of two configurations exchanged by a switch has a
proper successor), so it is vacuous and is not cited.

* `PinnedLimitAt.terminal_of_stationary_family`: for one configuration family `Φ` without proper
  successors whose actual fibre is homotopy equivalent to the finite fibre at `𝔭` of the fixed
  limit `L`, with either branch's data over `Φ`, that finite fibre has `dim H¹ = 1`. This is the
  terminal case of the fixed limit (tex 4976–4980, 5154–5159).
* `PinnedLimitAt.terminal_of_witness`: the same for the witness of the clause: if the clause at
  `𝔭` holds through a configuration family without proper successors, the finite fibre of `L` at
  `𝔭` has `dim H¹ = 1`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open CategoryTheory Filter NumberField IsDedekindDomain IsLocalRing Matrix Module
open ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Contrib.CloudB3RC53
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.UniformSwitch ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Manuscript.RC.Uniform (Lambda finPlane lambdaHalfToFrac)
open ZInQ.Manuscript.RC.Limits (stageIdeal stageIdeal_tendsToZero)
open ZInQ.Contrib.RC53Assist.InnerLimit (fibreLimitGlobal finiteLimitSide)
open ZInQ.Manuscript.RC.CoefModules (ActualConj IsOpenKer CondAt Mcoef fullAt FullTorsion KS
  alphaChar quadChar)
open ZInQ.Manuscript.RC.LambdaCoef (HasFullTwoTorsion)
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Manuscript.RC.SelmerComplex (GKS Places Gloc locMap inflMap locMap_compat)
open ZInQ.Manuscript.RC.KummerMaps (actualKummerAtS IsLocallyQuadAt)
open ZInQ.Manuscript.RC.Wiring.StageSupport (condToMinS)
open ZInQ.Contrib.RC53Assist.OldOrthogonality.SupportCoefficients (characterAfterSupport)
open ZInQ.Contrib.RC53Assist.InnerLimitMoving (IntegralMatrixStageData selmerStages
  derivativeDiagram retainedRestrictionStages)
open ZInQ.Contrib.CloudB3RC53.CST (newformLevel)
open ZInQ.Manuscript.RC.Rings (isDiscreteValuationRing_atPrime_of_height_one)
open scoped PowerSeries.WithPiTopology

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {Cn : ActualConj K S} {W : WeierstrassCurve K} {hW : W.map (Cn.κ : K →+* K) = W}
  [W.IsElliptic] [HasFullTwoTorsion K S W] {ℓ : ℕ} {Q : Finset ℕ}

/-- **The collapse is the terminal case of the fixed limit** (tex 4976–4980, 5154–5159): for a
configuration family `Φ` without proper successors whose actual fibre is homotopy equivalent to
the finite fibre at `𝔭` of the fixed limit `L` of the address's moving family, with either
branch's data over `Φ` (the linked switches on the label families of the address, or the
homology-level data), that finite fibre has `dim H¹ = 1`. Kind: PROVED. -/
theorem PinnedLimitAt.terminal_of_stationary_family {Ψ : FamilyMovingCharacter K ℓ Q} {h : ℤ}
    {A : AddressMovingFamilyR Ψ h W} {L : MovingRetainedLimit A.Fam} {u : FractionRing Lambda}
    {P : Ideal Lambda} [P.IsPrime] (hP : P.height = 1)
    (Φ : SwitchFamily (ResAt P) (Localization.AtPrime P)) (hstat : ∀ c p, Φ.next c p = c)
    (e : HomotopyEquiv (selCx (Φ.fibre Φ.actual)).toCC (L.finiteFibre P).toCC)
    (hb : Nonempty (InnerLimitSwitchPinnedOn P Cn hW ℓ h A.Fam Φ (UniformSwitch.toFracAt P) u) ∨
      Nonempty (HomologySwitchDataPK Φ (UniformSwitch.toFracAt P) (resAt P) u)) :
    finrank (ResAt P) ((L.finiteFibre P).toCC.homology 1) = 1 := by
  have hA : finrank (ResAt P) ((selCx (Φ.fibre Φ.actual)).toCC.homology 1) = 1 := by
    rcases hb with hX | hG
    · obtain ⟨X⟩ := hX
      rw [← X.toSwitchModelFrame.fiberDim_eq Φ.actual]
      exact X.fiberDim_eq_one_of_stationary hP (UniformSwitch.toFracAt_injective P) hstat
    · obtain ⟨G⟩ := hG
      rw [← fiberDim_eq_h1 (ResAt P) (Localization.AtPrime P) (FractionRing Lambda)
        (UniformSwitch.toFracAt P) (resAt P) (G.stage Φ.actual) (Φ.fibre Φ.actual)
        ⟨G.model Φ.actual⟩]
      exact G.fiberDim_eq_one_of_stationary hP hstat
  rw [← hA]
  exact ((e.toHomologyIso 1).toLinearEquiv).finrank_eq.symm

variable (Cn hW) in
/-- **The clause through a stationary witness** (tex 4976–4980, 5154–5159): the pinned clause at
`𝔭` with its configuration family required to have no proper successors. Kind: definition. -/
def PinnedLimitAtStationary {Ψ : FamilyMovingCharacter K ℓ Q} {h : ℤ}
    (A : AddressMovingFamilyR Ψ h W) (L : MovingRetainedLimit A.Fam) (u : FractionRing Lambda)
    (P : Ideal Lambda) [P.IsPrime] : Prop :=
  ∃ Φ : SwitchFamily (ResAt P) (Localization.AtPrime P), (∀ c p, Φ.next c p = c) ∧
    IsGenuineFamilyAt P Φ ∧
    ∃ Dfin : IntegralMatrixStageData stageIdeal_tendsToZero L.hU
        (algebraMap Lambda (Localization.AtPrime P)) (UniformSwitch.toFracAt P)
        (selmerStages (derivativeDiagram L.C (retainedRestrictionStages L.D) .finite)),
      Nonempty (HomotopyEquiv (selCx (Φ.fibre Φ.actual)).toCC (L.finiteFibre P).toCC) ∧
      ((∃ X : InnerLimitSwitchPinnedOn P Cn hW ℓ h A.Fam Φ (UniformSwitch.toFracAt P) u,
          X.stage Φ.actual = Dfin.stage) ∨
        (Φ.quadratic (resAt P) ∧
          ∃ G : HomologySwitchDataPK Φ (UniformSwitch.toFracAt P) (resAt P) u,
            G.stage Φ.actual = Dfin.stage))

/-- A stationary witness is a witness of the pinned clause. Kind: PROVED. -/
theorem PinnedLimitAtStationary.toPinned {Ψ : FamilyMovingCharacter K ℓ Q} {h : ℤ}
    {A : AddressMovingFamilyR Ψ h W} {L : MovingRetainedLimit A.Fam} {u : FractionRing Lambda}
    {P : Ideal Lambda} [P.IsPrime] (hI : PinnedLimitAtStationary Cn hW A L u P) :
    PinnedLimitAt Cn hW A L u P := by
  obtain ⟨Φ, -, hΦ, Dfin, he, hb⟩ := hI
  exact ⟨Φ, hΦ, Dfin, he, hb⟩

/-- **The collapse through the witness** (tex 4976–4980, 5154–5159): if the pinned clause at a
height-one `𝔭` holds through a configuration family without proper successors, the finite fibre
at `𝔭` of the fixed limit `L` has `dim H¹ = 1` (`terminal_of_stationary_family`). Kind: PROVED. -/
theorem PinnedLimitAt.terminal_of_witness {Ψ : FamilyMovingCharacter K ℓ Q} {h : ℤ}
    {A : AddressMovingFamilyR Ψ h W} {L : MovingRetainedLimit A.Fam} {u : FractionRing Lambda}
    {P : Ideal Lambda} [P.IsPrime] (hP : P.height = 1)
    (hI : PinnedLimitAtStationary Cn hW A L u P) :
    finrank (ResAt P) ((L.finiteFibre P).toCC.homology 1) = 1 := by
  obtain ⟨Φ, hstat, -, Dfin, ⟨e⟩, hb⟩ := hI
  refine PinnedLimitAt.terminal_of_stationary_family (Cn := Cn) (hW := hW) (u := u) hP Φ hstat e
    ?_
  rcases hb with ⟨X, -⟩ | ⟨-, G, -⟩
  · exact Or.inl ⟨X⟩
  · exact Or.inr ⟨G⟩

end ZInQ.Manuscript.RC.Wiring
